module Termination.TagSet (
        embedWithTagSets
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.Syntax

import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M


type TagSet = FinSet

embedWithTagSets :: WQO State Generaliser
embedWithTagSets = precomp stateTags $ postcomp (const generaliseNothing) equal
  where
    stateTags :: State -> TagSet
    stateTags (_, Heap h _, k, (_, e)) =
      -- traceRender ("stateTags (TagSet)", M.map heapBindingTagSet h, map stackFrameTag' k, qaTag' e) $
        pureHeapTagSet h `IS.union` stackTagSet k `IS.union` tagTagSet (qaTag' e)

heapBindingTagSet :: HeapBinding -> TagSet
heapBindingTagSet = maybe IS.empty (tagTagSet . pureHeapBindingTag') . heapBindingTag

pureHeapTagSet :: PureHeap -> IS.IntSet
pureHeapTagSet = IS.unions . map heapBindingTagSet . M.elems

stackTagSet :: Stack -> IS.IntSet
stackTagSet = IS.fromList . map (tagInt . stackFrameTag')

tagTagSet :: Tag -> IS.IntSet
tagTagSet = IS.singleton . tagInt
