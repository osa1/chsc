module Termination.Extras (
    partitionedRefinement,
    subGraphGeneralisation
  ) where

import IGraph
import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Graph.Wrapper as G
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.List (mapAccumL)
import qualified Data.Map as M
import qualified Data.Set as S

import Termination.Generaliser
import Termination.Terminate

import Core.FreeVars (FreeVars)
import Core.Renaming (Out)
import Core.Syntax (Var)

import Evaluator.FreeVars
import Evaluator.Syntax

partitionedRefinement :: WQO State Generaliser -> WQO State Generaliser
partitionedRefinement wqo = precomp (id &&& statePartitioning) $ postcomp fst $ prod wqo equal
  where
    statePartitioning :: State -> S.Set (S.Set Fin)
    statePartitioning (_, Heap h _, k, (_, qa)) = result
      where
        -- All of the variables referenced by a particular tag
        tag_references = IM.unionsWith S.union $ [IM.singleton (tagInt (annedTag e)) (inFreeVars annedTermFreeVars in_e) | hb <- M.elems h, Just in_e@(_, e) <- [heapBindingTerm hb]] ++
                                                 [IM.singleton (tagInt (tag kf)) (stackFrameFreeVars (tagee kf)) | kf <- k] ++
                                                 [IM.singleton (tagInt (annedTag qa)) (annedTermFreeVars' (qaToAnnedTerm' (annee qa)))]

        -- Inverting the above mapping, all the tags that reference a particular variable
        referencing_tags = M.unionsWith S.union [M.singleton x (S.singleton i) | (i, xs) <- IM.toList tag_references, x <- S.toList xs]

        -- Those variables with no attached information
        xs_no_infos = M.keysSet $ M.filter (\hb -> isNothing (heapBindingTerm hb)) h

        -- Use graphs to compute groups of tags that refer to overlapping sets of xs_no_infos
        sccs = G.stronglyConnectedComponents $ G.fromListSimple [(Fin tg, [Fin other_tg | x <- S.toList (xs `S.intersection` xs_no_infos), Just other_tgs <- [M.lookup x referencing_tags], other_tg <- S.elems other_tgs]) | (tg, xs) <- IM.toList tag_references]

        -- Turn those SCCs into simple sets
        result = S.fromList [S.fromList (Foldable.toList scc) | scc <- sccs]


data NodeIdentity = QANode | HeapNode (Out Var) | StackNode Int
                  deriving (Eq, Ord, Show)

instance Pretty NodeIdentity where
    pPrintPrec _prec _level QANode        = text "<qa>"
    pPrintPrec prec  level  (HeapNode x') = pPrintPrec prec level x'
    pPrintPrec prec  level  (StackNode i) = pPrintPrec prec level i


subGraphGeneralisation :: WQO State Generaliser -> WQO State Generaliser
subGraphGeneralisation = postcomp stateSubGraphs . what
  where
    stateSubGraphs :: ((State, State), Generaliser) -> Generaliser
    stateSubGraphs ((s1, s2), growing_generaliser) = fromMaybe growing_generaliser mb_subgraph_generaliser
      where
        stateToGraph :: State -> G.Graph NodeIdentity Color
        stateToGraph (_, Heap h _, k, in_qa@(_, qa)) = G.fromListLenient $ heap_fragment ++ stack_fragment ++ qa_fragment
          where
            named_k = [0..] `zip` k

            lookupVarNode :: Out Var -> Maybe NodeIdentity
            lookupVarNode = \x' -> M.lookup x' mapping
              where
                mapping = M.fromList $ [(x', StackNode i) | (i, kf) <- named_k, Update x' <- [tagee kf]] ++
                                       [(x', HeapNode x') | x' <- M.keys h]

            lookupVarNodes :: FreeVars -> [NodeIdentity]
            lookupVarNodes = mapMaybe lookupVarNode . S.toList

            heap_fragment = [(HeapNode x', tagInt (pureHeapBindingTag' (annedTag e)), lookupVarNodes (inFreeVars annedTermFreeVars in_e)) | (x', hb) <- M.toList h, Just in_e@(_, e) <- [heapBindingTerm hb]]
            stack_fragment = snd $ mapAccumL (\inner_node (i, kf) -> (StackNode i, (StackNode i, tagInt (stackFrameTag' kf), inner_node : lookupVarNodes (stackFrameFreeVars (tagee kf))))) QANode named_k
            qa_fragment = [(QANode, tagInt (qaTag' qa), lookupVarNodes (inFreeVars annedFreeVars in_qa))]

        mb_subgraph_generaliser = do
            let g1 = stateToGraph s1
                g2 = stateToGraph s2
            traceRender (text "subgraph-generaliser: try" $$ hang (text "g1") 2 (vcat $ map pPrint (G.toList g1)) $$ hang (text "g2") 2 (vcat $ map pPrint (G.toList g2))) $ return ()

            subiso <- listToMaybe (subgraphIsomorphisms g1 g2)
            -- The idea is that we should drop stuff that is tagged like the
            -- part of the graph that we dropped to get the subgraph
            -- isomorphism. In fact, we only want to generalise the *first* such
            -- thing we come across (in a dependency sense) or we will
            -- residualise too much, but let the splitter worry about that!
            -- FIXME: not sufficient
            let retained_nodes2 = S.fromList (M.elems subiso)
                -- Try to trim exactly those tags that are on the boundary
                -- between retained and unretained:
                -- retained_point_to =
                --   S.fromList [adjacent | (node, color, adjacents) <- G.toList g2
                --                        , node `S.member` retained_nodes2
                --                        , adjacent <- adjacents]
                dropped_colors =
                  IS.fromList [color | (node, color, _adjacents) <- G.toList g2
                                     , not (node `S.member` retained_nodes2)
                                     -- , node `S.member` retained_point_to
                                     --     || any (`S.member` retained_nodes2) adjacents
                                     ]

            traceRender (hang (text "subgraph-generaliser: has subiso") 2 $
              pPrint dropped_colors $$ pPrint subiso) $ return ()

            -- FIXME: not great because it might still lead to a trivial
            -- generaliser at the split stage.. use a list of generalisers
            -- instead?
            guard (not (IS.null dropped_colors))

            -- FIXME: I should check that the proposed dropped tags are in the
            -- original state. Reason: with rollback we will generalise the
            -- original state, and it would be sad if none of the tags helped me
            -- to generalise that guy...
            return $ generaliserFromFinSet dropped_colors
