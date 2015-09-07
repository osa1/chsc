module Termination.Generaliser where

import Core.Renaming (Out)
import Core.Syntax (Var)

import Evaluator.Syntax

import Utilities (FinMap, FinSet, Tag, Tagged, injectTag, tag, tagInt)

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS


data Generaliser = Generaliser
  { generaliseStackFrame  :: Tagged StackFrame -> Bool
  , generaliseHeapBinding :: Out Var -> HeapBinding -> Bool
  }

generaliseNothing :: Generaliser
generaliseNothing = Generaliser (\_ -> False) (\_ _ -> False)

generaliserFromGrowing :: FinMap Bool -> Generaliser
generaliserFromGrowing = generaliserFromFinSet . IM.keysSet . IM.filter id

generaliserFromFinSet :: FinSet -> Generaliser
generaliserFromFinSet generalise_what = Generaliser
    { generaliseStackFrame  =
        \kf   -> should_generalise (stackFrameTag' kf)
    , generaliseHeapBinding =
        \_ hb -> maybe False (should_generalise . pureHeapBindingTag') $ heapBindingTag hb
    }
  where
    should_generalise tg = IS.member (tagInt tg) generalise_what

pureHeapBindingTag' :: Tag -> Tag
pureHeapBindingTag' = injectTag 5

stackFrameTag' :: Tagged StackFrame -> Tag
stackFrameTag' = injectTag 3 . tag

qaTag' :: Anned QA -> Tag
qaTag' = injectTag 2 . annedTag
