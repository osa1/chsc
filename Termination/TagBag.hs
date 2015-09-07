{-# LANGUAGE Rank2Types #-}

module Termination.TagBag
  ( embedWithTagBags
  ) where

import Termination.Generaliser
import Termination.Terminate (Prearrow (..), WQO, nat, natsWeak,
                              refineCollection, zippable)

import Evaluator.Syntax

import StaticFlags (TagBagType (..))
import Utilities

import qualified Data.IntMap as IM
import qualified Data.Map as M


type TagBag = FinMap Nat

embedWithTagBags :: TagBagType -> WQO State Generaliser
embedWithTagBags tbt
  | tagBagPairwiseGrowth tbt = embedWithTagBags' (zippable nat)
  | otherwise                = embedWithTagBags' natsWeak

embedWithTagBags'
  :: (forall f . (Foldable f, Traversable f, Zippable f) => WQO (f Nat) (f Bool))
  -> WQO State Generaliser
embedWithTagBags' nats =
    precomp stateTags $ postcomp generaliserFromGrowing $
      refineCollection (\discard -> postcomp discard nats)
  where
    stateTags :: State -> TagBag
    stateTags (_, Heap h _, k, (_, qa)) =
     -- traceRender ("stateTags (TagBag)", M.map heapBindingTagBag h, map stackFrameTag' k, qaTag' qa) $
     -- traceRender ("stateTags:heap (TagBag)", M.map heapBindingTag h) $
     (\res -> traceRender ("stateTags (TagBag)", res) res) $
       pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` tagTagBag (qaTag' qa)

heapBindingTagBag :: HeapBinding -> TagBag
heapBindingTagBag = maybe (mkTagBag []) (tagTagBag . pureHeapBindingTag') . heapBindingTag

pureHeapTagBag :: PureHeap -> TagBag
pureHeapTagBag = plusTagBags . map heapBindingTagBag . M.elems

stackTagBag :: Stack -> TagBag
stackTagBag = mkTagBag . map stackFrameTag'

tagTagBag :: Tag -> TagBag
tagTagBag = mkTagBag . return

mkTagBag :: [Tag] -> TagBag
mkTagBag = plusTagBags . map (\(TG i occs) -> IM.singleton (unFin i) occs)

plusTagBag :: TagBag -> TagBag -> TagBag
plusTagBag = IM.unionWith (+)

plusTagBags :: [TagBag] -> TagBag
plusTagBags = foldr plusTagBag IM.empty
