{-# LANGUAGE TypeOperators #-}
module Evaluator.Syntax where

import Evaluator.Deeds

import Core.FreeVars
import Core.Renaming
import Core.Size
import Core.Syntax
import Core.Tag

import Renaming
import Utilities

import Data.Copointed
import Data.Functor.Compose
import Data.List (foldl')
import qualified Data.Map as M

type Anned = Compose Tagged (Compose Sized FVed)
type AnnedTerm = Anned (TermF Anned)
type AnnedValue = ValueF Anned
type AnnedAlt = AltF Anned

annee :: Anned a -> a
annee = copoint

annedSize :: Anned a -> Size
annedSize = size . getCompose . tagee . getCompose

annedFreeVars :: Anned a -> FreeVars
annedFreeVars = freeVars . sizee . getCompose . tagee . getCompose

annedTag :: Anned a -> Tag
annedTag = tag . getCompose


annedVarFreeVars' = taggedSizedFVedVarFreeVars'
annedTermFreeVars = taggedSizedFVedTermFreeVars
annedTermFreeVars' = taggedSizedFVedTermFreeVars'
annedValueFreeVars = taggedSizedFVedValueFreeVars
annedValueFreeVars' = taggedSizedFVedValueFreeVars'
annedAltsFreeVars = taggedSizedFVedAltsFreeVars

annedVarSize' = taggedSizedFVedVarSize'
annedTermSize' = taggedSizedFVedTermSize'
annedTermSize = taggedSizedFVedTermSize
annedValueSize' = taggedSizedFVedValueSize'
annedValueSize = taggedSizedFVedValueSize
annedAltsSize = taggedSizedFVedAltsSize

renameAnnedTerm = renameTaggedSizedFVedTerm :: IdSupply -> Renaming -> AnnedTerm -> AnnedTerm
renameAnnedValue = renameTaggedSizedFVedValue
renameAnnedValue' = renameTaggedSizedFVedValue'
renameAnnedAlts = renameTaggedSizedFVedAlts

detagAnnedTerm = taggedSizedFVedTermToFVedTerm
detagAnnedValue = taggedSizedFVedValueToFVedValue
detagAnnedValue' = taggedSizedFVedValue'ToFVedValue'
detagAnnedAlts = taggedSizedFVedAltsToFVedAlts


annedVar :: Tag -> Var -> Anned Var
annedVar   tg x = Compose (Tagged tg (Compose (Sized (annedVarSize' x)   (FVed (annedVarFreeVars' x)  x))))

annedTerm :: Tag -> TermF Anned -> AnnedTerm
annedTerm  tg e = Compose (Tagged tg (Compose (Sized (annedTermSize' e)  (FVed (annedTermFreeVars' e)  e))))

annedValue :: Tag -> ValueF Anned -> Anned AnnedValue
annedValue tg v = Compose (Tagged tg (Compose (Sized (annedValueSize' v) (FVed (annedValueFreeVars' v) v))))


toAnnedTerm :: IdSupply -> Term -> AnnedTerm
toAnnedTerm tag_ids = tagFVedTerm tag_ids . reflect


data QA
  = Question Var
  | Answer   (ValueF Anned)

instance Pretty QA where
    pPrintPrec level prec = pPrintPrec level prec . qaToAnnedTerm'

qaToAnnedTerm' :: QA -> TermF Anned
qaToAnnedTerm' (Question x) = Var x
qaToAnnedTerm' (Answer v)   = Value v


type UnnormalisedState = (Deeds, Heap, Stack, In AnnedTerm)
type State             = (Deeds, Heap, Stack, In (Anned QA))

denormalise :: State -> UnnormalisedState
denormalise (deeds, h, k, (rn, qa)) = (deeds, h, k, (rn, fmap qaToAnnedTerm' qa))


-- Invariant: LetBound things cannot refer to LambdaBound things.
--
-- This is motivated by:
--  1. There is no point lambda-abstracting over things referred to by LetBounds
--     because the resulting h-function would be trapped under the appropriate
--     let-binding anyway, at which point all the lambda-abstracted things would
--     be in scope as FVs.
--  2. It allows (but does not require) the matcher to look into the RHS of
--     LetBound stuff (rather than just doing nominal matching).
data HowBound = InternallyBound | LambdaBound | LetBound
              deriving (Eq, Show)

instance Pretty HowBound where
    pPrint = text . show

data HeapBinding = HB { howBound :: HowBound, heapBindingMeaning :: Either (Maybe Tag) (In AnnedTerm) }

instance Pretty HeapBinding where
    pPrintPrec level prec (HB how mb_in_e) = case how of
        InternallyBound -> either (const empty) (pPrintPrec level prec . renameIn (renameAnnedTerm prettyIdSupply)) mb_in_e
        LambdaBound     -> text "λ" <> angles (either (const empty) (pPrintPrec level noPrec . renameIn (renameAnnedTerm prettyIdSupply)) mb_in_e)
        LetBound        -> text "l" <> angles (either (const empty) (pPrintPrec level noPrec . renameIn (renameAnnedTerm prettyIdSupply)) mb_in_e)

lambdaBound :: HeapBinding
lambdaBound = HB LambdaBound (Left Nothing)

internallyBound :: In AnnedTerm -> HeapBinding
internallyBound in_e = HB InternallyBound (Right in_e)

environmentallyBound :: Tag -> HeapBinding
environmentallyBound tg = HB LetBound (Left (Just tg))

type PureHeap = M.Map (Out Var) HeapBinding

data Heap = Heap PureHeap IdSupply

instance Pretty Heap where
    pPrintPrec level prec (Heap h _) = pPrintPrec level prec h


type Stack = [Tagged StackFrame]

data StackFrame
  = Apply (Out Var)
  | Scrutinise (In [AnnedAlt])
  | PrimApply PrimOp [In (Anned AnnedValue)] [In AnnedTerm]
  | Update (Out Var)

instance Pretty StackFrame where
    pPrintPrec level prec kf = case kf of
        Apply x'                  -> pPrintPrecApp level prec (text "[_]") x'
        Scrutinise in_alts        -> pPrintPrecCase level prec (text "[_]") (renameIn (renameAnnedAlts prettyIdSupply) in_alts)
        PrimApply pop in_vs in_es -> pPrintPrecPrimOp level prec pop (map SomePretty in_vs ++ map SomePretty in_es)
        Update x'                 -> pPrintPrecApp level prec (text "update") x'


heapBindingTerm :: HeapBinding -> Maybe (In AnnedTerm)
heapBindingTerm = either (const Nothing) Just . heapBindingMeaning

heapBindingTag :: HeapBinding -> Maybe Tag
heapBindingTag = either id (Just . annedTag . snd) . heapBindingMeaning

-- | Size of HeapBinding for Deeds purposes
heapBindingSize :: HeapBinding -> Size
heapBindingSize (HB InternallyBound (Right (_, e))) = annedSize e
heapBindingSize _                                   = 0

-- | Size of StackFrame for Deeds purposes
stackFrameSize :: StackFrame -> Size
stackFrameSize kf = 1 + case kf of
    Apply _                 -> 0
    Scrutinise (_, alts)    -> annedAltsSize alts
    PrimApply _ in_vs in_es -> sum (map (annedValueSize . snd) in_vs ++ map (annedTermSize . snd) in_es)
    Update _                -> 0

stateSize :: State -> Size
stateSize (_deeds, h, k, in_qa) = heapSize h + stackSize k + qaSize (snd in_qa)
          where qaSize = annedSize . fmap qaToAnnedTerm'
                heapSize (Heap h _) = sum (map heapBindingSize (M.elems h))
                stackSize = sum . map (stackFrameSize . tagee)

addStateDeeds :: Deeds -> (Deeds, Heap, Stack, In (Anned a)) -> (Deeds, Heap, Stack, In (Anned a))
addStateDeeds extra_deeds (deeds, h, k, in_e) = (extra_deeds + deeds, h, k, in_e)

releaseHeapBindingDeeds :: Deeds -> HeapBinding -> Deeds
releaseHeapBindingDeeds deeds hb = deeds + heapBindingSize hb

releasePureHeapDeeds :: Deeds -> PureHeap -> Deeds
releasePureHeapDeeds = M.fold (flip releaseHeapBindingDeeds)

releaseStackDeeds :: Deeds -> Stack -> Deeds
releaseStackDeeds = foldl' (\deeds kf -> deeds + stackFrameSize (tagee kf))

releaseStateDeed :: (Deeds, Heap, Stack, In (Anned a)) -> Deeds
releaseStateDeed (deeds, Heap h _, k, (_, e)) = releaseStackDeeds (releasePureHeapDeeds (deeds + annedSize e) h) k
