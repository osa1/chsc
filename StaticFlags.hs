module StaticFlags where

import Data.Char (toLower)
import Data.Maybe
import Data.List (intercalate, stripPrefix)

import System.Environment
import System.IO.Unsafe
import System.Process


{-# NOINLINE cODE_IDENTIFIER #-}
cODE_IDENTIFIER :: String
cODE_IDENTIFIER = head $ lines $ unsafePerformIO (readProcess "git" ["log", "--format=%H", "-1"] "")

{-# NOINLINE rUN_IDENTIFIER #-}
rUN_IDENTIFIER :: String
rUN_IDENTIFIER = intercalate " " [filter (/= '-') arg | '-':'-':arg <- unsafePerformIO getArgs]

tIMEOUT_SECONDS :: Int
tIMEOUT_SECONDS = 120

{-# NOINLINE tICKY #-}
tICKY :: Bool
tICKY = "--ticky" `elem` unsafePerformIO getArgs

{-# NOINLINE nO_OPTIMISATIONS #-}
nO_OPTIMISATIONS :: Bool
nO_OPTIMISATIONS = "-O0" `elem` unsafePerformIO getArgs

{-# NOINLINE gHC_OPTIONS #-}
gHC_OPTIONS :: [String]
gHC_OPTIONS = [opt | arg <- unsafePerformIO getArgs, Just ('=':opt) <- [stripPrefix "--ghc-option" arg]]


{-# NOINLINE aSSERTIONS #-}
aSSERTIONS :: Bool
aSSERTIONS = not $ "--no-assertions" `elem` unsafePerformIO getArgs

{-# NOINLINE qUIET #-}
qUIET :: Bool
qUIET = "-v0" `elem` unsafePerformIO getArgs

{-# NOINLINE rEDUCE_TERMINATION_CHECK #-}
rEDUCE_TERMINATION_CHECK :: Bool
rEDUCE_TERMINATION_CHECK = not $ "--no-reduce-termination" `elem` unsafePerformIO getArgs

{-# NOINLINE eVALUATE_PRIMOPS #-}
eVALUATE_PRIMOPS :: Bool
eVALUATE_PRIMOPS = not $ "--no-primops" `elem` unsafePerformIO getArgs

{-# NOINLINE dEEDS #-}
dEEDS :: Bool
dEEDS = not $ "--no-deeds" `elem` unsafePerformIO getArgs

parseEnum :: String -> a -> [(String, a)] -> a
parseEnum prefix def opts = fromMaybe def $ listToMaybe [parse opt | arg <- unsafePerformIO getArgs, Just ('=':opt) <- [stripPrefix prefix arg]]
  where parse = fromJust . flip lookup opts . map toLower

data DeedsPolicy = FCFS | Proportional
                 deriving (Read)

{-# NOINLINE dEEDS_POLICY #-}
dEEDS_POLICY :: DeedsPolicy
dEEDS_POLICY = parseEnum "--deeds-policy" Proportional [("fcfs", FCFS), ("proportional", Proportional)]

data TagBagType = TBT { tagBagPairwiseGrowth :: Bool, tagBagPartitionedRefinement :: Bool, tagBagSubGraph :: Bool }
                deriving (Show)
data TagCollectionType = TagBag TagBagType | TagGraph | TagSet
                   deriving (Show)

{-# NOINLINE tAG_COLLECTION #-}
tAG_COLLECTION :: TagCollectionType
tAG_COLLECTION = parseEnum "--tag-collection" (TagBag (TBT False False True)) [("bags", TagBag (TBT False False False)), ("bags-strong", TagBag (TBT True False False)), ("bags-strongest", TagBag (TBT True True False)), ("bags-subgraph", TagBag (TBT False False True)), ("graphs", TagGraph), ("sets", TagSet)]

data GeneralisationType = NoGeneralisation | AllEligible | DependencyOrder Bool

{-# NOINLINE gENERALISATION #-}
gENERALISATION :: GeneralisationType
gENERALISATION = parseEnum "--generalisation" (DependencyOrder True) [("none", NoGeneralisation), ("all-eligible", AllEligible), ("first-reachable", DependencyOrder True), ("last-reachable", DependencyOrder False)]

{-# NOINLINE bLOAT_FACTOR #-}
bLOAT_FACTOR :: Int
bLOAT_FACTOR = fromMaybe 10 $ listToMaybe [read val | arg <- unsafePerformIO getArgs, Just val <- [stripPrefix "--bloat=" arg]]
 -- NB: need a bloat factor of at least 5 to get append/append fusion to work. The critical point is:
 --
 --  let (++) = ...
 --  in case (case xs of []     -> ys
 --                      (x:xs) -> x : (xs ++ ys)) of
 --    []     -> zs
 --    (x:xs) -> x : (xs ++ zs)
 --
 -- We need to duplicate the case continuation into each branch, so at one time we will have:
 --  1) Two copies of (++) in the [] branch of the inner case
 --    a) One in the heap
 --    b) One from the stack (from [_] ++ zs)
 --  2) Similarly two copies in the (:) branch of the inner case
 --  3) One copy manifested in the residual branch of xs
 --
 -- Total = 5 copies (due to tiebacks, the residual program will do better than this)
 --
 -- 
 -- Unfortunately, my implementation doesn't tie back as eagerly as you might like, so we actually peel the loop once and
 -- hence need a bloat factor of 8 here (5 + 3 other case statements derived from (++))
 -- TODO: figure out how to reduce this number.

{-# NOINLINE sPLITTER_CHEAPIFICATION #-}
sPLITTER_CHEAPIFICATION :: Bool
sPLITTER_CHEAPIFICATION = "--cheapification" `elem` unsafePerformIO getArgs
 -- TODO: test my hypothesis that given that we already do speculation, let-floating in the splitter won't make much difference

{-# NOINLINE sPECULATION #-}
sPECULATION :: Bool
sPECULATION = not $ "--no-speculation" `elem` unsafePerformIO getArgs

-- NB: may want to these definitions if you want to default speculation to off
    
-- {-# NOINLINE sPLITTER_CHEAPIFICATION #-}
-- sPLITTER_CHEAPIFICATION :: Bool
-- sPLITTER_CHEAPIFICATION = not $ "--no-cheapification" `elem` unsafePerformIO getArgs
-- 
-- {-# NOINLINE sPECULATION #-}
-- sPECULATION :: Bool
-- sPECULATION = "--speculation" `elem` unsafePerformIO getArgs

{-# NOINLINE lOCAL_TIEBACKS #-}
lOCAL_TIEBACKS :: Bool
lOCAL_TIEBACKS = not $ "--no-local-tiebacks" `elem` unsafePerformIO getArgs

{-# NOINLINE rEDUCE_ROLLBACK #-}
rEDUCE_ROLLBACK :: Bool
rEDUCE_ROLLBACK = not $ "--no-reduce-rollback" `elem` unsafePerformIO getArgs

{-# NOINLINE sC_ROLLBACK #-}
sC_ROLLBACK :: Bool
sC_ROLLBACK = not $ "--no-sc-rollback" `elem` unsafePerformIO getArgs

{-# NOINLINE dISCARD_FULFILMENTS_ON_ROLLBACK #-}
dISCARD_FULFILMENTS_ON_ROLLBACK :: Bool
dISCARD_FULFILMENTS_ON_ROLLBACK = "--discard-fulfilments-on-rollback" `elem` unsafePerformIO getArgs

{-# NOINLINE eXPAND_CASE_DEFAULTS #-}
eXPAND_CASE_DEFAULTS :: Bool
eXPAND_CASE_DEFAULTS = "--expand-case-defaults" `elem` unsafePerformIO getArgs

{-# NOINLINE eXPAND_CASE_UNCOVEREDS #-}
eXPAND_CASE_UNCOVEREDS :: Bool
eXPAND_CASE_UNCOVEREDS = "--expand-case-uncovereds" `elem` unsafePerformIO getArgs

{-# NOINLINE cALL_BY_NAME #-}
cALL_BY_NAME :: Bool
cALL_BY_NAME = "--call-by-name" `elem` unsafePerformIO getArgs

{-# NOINLINE pRETTIFY #-}
pRETTIFY :: Bool
pRETTIFY = "--prettify" `elem` unsafePerformIO getArgs

{-# NOINLINE dUPLICATE_VALUES_EVALUATOR #-}
{-# NOINLINE dUPLICATE_VALUES_SPLITTER #-}
dUPLICATE_VALUES_EVALUATOR, dUPLICATE_VALUES_SPLITTER :: Bool
dUPLICATE_VALUES_EVALUATOR = "--duplicate-values-evaluator" `elem` unsafePerformIO getArgs
dUPLICATE_VALUES_SPLITTER = "--duplicate-values-splitter" `elem` unsafePerformIO getArgs

{-# NOINLINE rEFINE_FULFILMENT_FVS #-}
rEFINE_FULFILMENT_FVS :: Bool
rEFINE_FULFILMENT_FVS = not $ "--no-refine-fulfilment-fvs" `elem` unsafePerformIO getArgs

{-# NOINLINE oCCURRENCE_GENERALISATION #-}
oCCURRENCE_GENERALISATION :: Bool
oCCURRENCE_GENERALISATION = not $ "--no-occurrence-generalisation" `elem` unsafePerformIO getArgs

{-# NOINLINE mATCH_REDUCED #-}
mATCH_REDUCED :: Bool
mATCH_REDUCED = not $ "--no-match-reduced" `elem` unsafePerformIO getArgs

{-# NOINLINE mATCH_SPECULATION #-}
mATCH_SPECULATION :: Bool
mATCH_SPECULATION = not $ "--no-match-speculation" `elem` unsafePerformIO getArgs
