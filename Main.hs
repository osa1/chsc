module Main (main) where

import Core.FreeVars
import Core.Parser
import Core.Size
import Core.Syntax

import Supercompile.Drive

import GHC
import Name
import StaticFlags
import Utilities

import Data.Char (toLower)
import Data.List (find, intercalate, isPrefixOf, partition)
import qualified Data.Set as S

import System.Directory
import System.Environment
import System.FilePath (dropExtension, replaceExtension, takeDirectory,
                        takeFileName, (</>))
import System.IO
import System.Timeout

import Numeric (showFFloat)

type Ways = (Bool, Bool)

-- The Cambridge Haskell Supercompiler (CHSC)
main :: IO ()
main = do
    hPutStrLn stderr $
      "Welcome to the Cool Cambridge Haskell Supercompiler (" ++ cODE_IDENTIFIER ++ ")"
    (flags, args) <- fmap (partition ("-" `isPrefixOf`)) getArgs
    putStrLn $ unwords flags
    case args of
      []            -> putStrLn "TODO: usage"
      ("ghc":files) -> test (True,  False) files
      ("raw":files) -> test (False, True)  files
      files         -> test (True,  True)  files

test :: Ways -> [FilePath] -> IO ()
test ways files = do
    putStrLn $ intercalate " & "
      ["Filename", "SC time", "Reduce-stops", "SC-stops",
       "Compile time", "Run time", "Heap size", "Term size"] ++ " \\\\"
    test_errors <-
      concatMapM (\file -> liftM (maybeToList . fmap (file,)) $ testOne ways file) files
    unless (null test_errors) $ do
      hPutStrLn stderr $ "WARNING: " ++ show (length test_errors) ++ " test failures:"
      mapM_ (\(fp, err) -> hPutStrLn stderr (fp ++ ": " ++ err)) test_errors

-- | Split a module into a definitions and tests.
splitModule :: [(Var, Term)] -> (Term, Maybe Term)
splitModule xes =
    ( letRecSmart (transitiveInline (S.singleton root)) (var root)
    , mkTestLet <$> mb_test
    )
  where
    findBinding :: String -> Maybe Name
    findBinding what = fst <$> find ((== what) . name_string . fst) xes

    transitiveInline :: S.Set Var -> [(Var, Term)]
    transitiveInline fvs
        | fvs == fvs' = need_xes
        | otherwise   = transitiveInline fvs'
      where
        need_xes = [(x, e) | (x, e) <- xes, x `S.member` fvs]
        fvs' = fvs `S.union` S.unions (map (termFreeVars . snd) need_xes)

    root    = expectJust "No root" $ findBinding "root"
    mb_test = findBinding "tests"

    mkTestLet :: Var -> Term
    mkTestLet t =
      letRecSmart (filter ((/= root) . fst) $ transitiveInline (S.singleton t)) (var t)

testOne :: Ways -> FilePath -> IO (Maybe String)
testOne (ghc_way, sc_way) file = do
    hPutStrLn stderr $ "% " ++ file
    (wrapper, binds) <- parse file
    case splitModule binds of
      (_, Nothing) -> hPutStrLn stderr "Skipping: no tests" >> return Nothing
      (e, Just test_e) -> do
        let escape = concatMap (\c -> if c == '_' then "\\_" else [c])
            benchmark = escape $ map toLower $ takeFileName $ dropExtension file

        case (ghc_way, sc_way) of
          (True, True) -> do
            ei_e_ghc_res <- tryGHC file wrapper e test_e
            ei_e_sc_res <- trySC file wrapper e test_e
            let (mb_err, mb_res) =
                  either (\err -> (Just err, Nothing)) (\res -> (Nothing, Just res)) $
                    liftM2 (,) ei_e_ghc_res ei_e_sc_res
            putStrLn $ showComparison benchmark mb_res
            return mb_err
          (True, False) -> do
            ei_e_ghc_res <- tryGHC file wrapper e test_e
            let (mb_err, mb_res) =
                  either (\err -> (Just err, Nothing)) (\res -> (Nothing, Just res)) ei_e_ghc_res
            putStrLn $ showRaw benchmark mb_res
            return mb_err
          (False, True) -> do
            ei_e_sc_res <- trySC file wrapper e test_e
            let (mb_err, mb_res) =
                  either (\err -> (Just err, Nothing)) (\res -> (Nothing, Just res)) ei_e_sc_res
            putStrLn $ showRaw benchmark mb_res
            return mb_err
          (False, False) -> error "testOne: invalid way"

tryGHC :: FilePath -- ^ Test file
       -> String   -- ^ Wrapper to add to the generated Haskell test file
       -> Term     -- ^ `root` definition
       -> Term     -- ^ `tests` definition
       -> IO (Either String ((Bytes, Seconds, Bytes, Seconds), Size, Maybe a))
tryGHC file wrapper e test_e = do
    (before_code, before_res) <- runCompiled wrapper e test_e

    -- Save a copy of the non-supercompiled code
    createDirectoryIfMissing True (takeDirectory $ "input" </> file)
    writeFile ("input" </> replaceExtension file ".hs") before_code

    return $ fmap (, termSize e, Nothing) before_res

trySC :: FilePath -- ^ Test file
      -> String   -- ^ Wrapper to add to the generated Haskell test file
      -> Term     -- ^ `root` definition
      -> Term     -- ^ `tests` definition
      -> IO (Either String ((Bytes, Seconds, Bytes, Seconds), Size, Maybe (Seconds, SCStats)))
trySC file wrapper e test_e = do
    -- TODO: Need to implement instances, disabling this for now.
    -- rnf e `seq` return ()
    let (stats, e') = supercompile e
    mb_super_t <- timeout (tIMEOUT_SECONDS * 1000000)
                          (time_ (e' `seq` return ()))
                          -- TODO: Enable this
                          -- (time_ (rnf e' `seq` return ()))
    case mb_super_t of
      Nothing -> return $ Left "Supercompilation timeout"
      Just super_t -> do
        (after_code, after_res) <- runCompiled wrapper e' test_e

        -- Save a copy of the supercompiled code
        let output_dir = "output" </> cODE_IDENTIFIER </> rUN_IDENTIFIER
        createDirectoryIfMissing True (takeDirectory $ output_dir </> file)
        writeFile (output_dir </> replaceExtension file ".hs") $
          unlines ["-- Code: " ++ cODE_IDENTIFIER,
                   "-- Run: " ++ rUN_IDENTIFIER, "", after_code]

        return $ fmap (, termSize e', Just (super_t, stats)) after_res

showRaw
  :: String
     -- ^ Benchmark name
  -> Maybe ((Bytes, Seconds, Bytes, Seconds), Int, Maybe (Seconds, SCStats))
     -- ^ Benchmark result
  -> String
showRaw benchmark mb_res =
    intercalate " & " (benchmark:fields) ++ " \\\\"
  where
    fields =
      case mb_res of
        Just ((_size, compile_t, heap_size, run_t), term_size, mb_super_t) ->
          maybe ["", "", ""] (\(super_t, stats) -> [ show super_t
                                                   , show (stat_reduce_stops stats)
                                                   , show (stat_sc_stops stats)
                                                   ]) mb_super_t
            ++ [show compile_t, show run_t, show heap_size, show term_size]
        Nothing -> ["", "", "", "", "", "", ""]

showComparison benchmark mb_res = intercalate " & " (benchmark:fields) ++ " \\\\"
  where
    fields =
      case mb_res of
        Just (( (_before_size, before_compile_t, before_heap_size, before_run_t)
              , before_term_size
              , Nothing ),
              ( (_after_size,  after_compile_t,  after_heap_size,  after_run_t)
              , after_term_size,  Just (after_super_t, after_stats) )
             ) -> [ dp1 after_super_t ++ "s"
                  , show (stat_reduce_stops after_stats)
                  , show (stat_sc_stops after_stats)
                  , dp2 (after_compile_t / before_compile_t)
                  , dp2 (after_run_t / before_run_t)
                  , dp2 (after_heap_size `ratio` before_heap_size)
                  , dp2 (after_term_size `ratio` before_term_size)
                  ]
        _ -> ["", "", "", "", "", "", ""]

    dp1 x = showFFloat (Just 1) x ""
    dp2 x = showFFloat (Just 2) x ""
    ratio n m = fromIntegral n / fromIntegral m :: Double
