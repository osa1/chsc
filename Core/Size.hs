{-# LANGUAGE FlexibleInstances, Rank2Types, TypeOperators #-}
module Core.Size where

import Utilities

import Control.Monad.Identity
import Data.Functor.Compose

import Core.FreeVars
import Core.Syntax

type SizedTerm = Sized (TermF Sized)

type SizedFVedTerm = (Compose Sized FVed) (TermF (Compose Sized FVed))
type SizedFVedAlt = AltF (Compose Sized FVed)
type SizedFVedValue = ValueF (Compose Sized FVed)

type TaggedSizedFVedTerm =
  (Compose Tagged (Compose Sized FVed)) (TermF (Compose Tagged (Compose Sized FVed)))
type TaggedSizedFVedAlt = AltF (Compose Tagged (Compose Sized FVed))
type TaggedSizedFVedValue = ValueF (Compose Tagged (Compose Sized FVed))


(varSize',
 termSize,
 termSize',
 altsSize,
 valueSize,
 valueSize') = mkSize (\f (Identity e) -> f e)

(fvedVarSize',
 fvedTermSize,
 fvedTermSize',
 fvedAltsSize,
 fvedValueSize,
 fvedValueSize') = mkSize (\f (FVed _ e) -> f e)

(sizedVarSize',
 sizedTermSize,
 sizedTermSize',
 sizedAltsSize,
 sizedValueSize,
 sizedValueSize') = mkSize (\_ (Sized sz _) -> sz)

(sizedFVedVarSize',
 sizedFVedTermSize,
 sizedFVedTermSize',
 sizedFVedAltsSize,
 sizedFVedValueSize,
 sizedFVedValueSize') = mkSize (\_ (Compose (Sized sz (FVed _ _))) -> sz)

(taggedSizedFVedVarSize',
 taggedSizedFVedTermSize,
 taggedSizedFVedTermSize',
 taggedSizedFVedAltsSize,
 taggedSizedFVedValueSize,
 taggedSizedFVedValueSize') = mkSize (\_ (Compose (Tagged _ (Compose (Sized sz (FVed _ _))))) -> sz)

{-# INLINE mkSize #-}
mkSize :: (forall a. (a -> Size) -> ann a -> Size)
       -> (Var              -> Size,
           ann (TermF ann)  -> Size,
           TermF ann        -> Size,
           [AltF ann]       -> Size,
           ann (ValueF ann) -> Size,
           ValueF ann       -> Size)
mkSize rec = (var', term, term', alternatives, value, value')
  where
    var' = const 0

    term = rec term'
    term' e = 1 + case e of
        Var x        -> var' x
        Value v      -> value' v - 1 -- Slight hack here so that we don't get +2 size on values
        App e x      -> term e + var' x
        PrimOp _ es  -> sum (map term es)
        Case e alts  -> term e + alternatives alts
        LetRec xes e -> sum (map (term . snd) xes) + term e

    value = rec value'
    value' v = 1 + case v of
        Indirect _ -> 0
        Lambda _ e -> term e
        Data _ _   -> 0
        Literal _  -> 0

    alternatives = sum . map alternative

    alternative = term . snd


instance Symantics Sized where
    var = sizedTerm . Var
    value = sizedTerm . Value
    app e = sizedTerm . App e
    primOp pop = sizedTerm . PrimOp pop
    case_ e = sizedTerm . Case e
    letRec xes e = sizedTerm (LetRec xes e)

sizedTerm :: TermF Sized -> SizedTerm
sizedTerm e = Sized (sizedTermSize' e) e


instance Symantics (Compose Sized FVed) where
    var = sizedFVedTerm . Var
    value = sizedFVedTerm . Value
    app e = sizedFVedTerm . App e
    primOp pop = sizedFVedTerm . PrimOp pop
    case_ e = sizedFVedTerm . Case e
    letRec xes e = sizedFVedTerm (LetRec xes e)

sizedFVedVar :: Var -> (Compose Sized FVed) Var
sizedFVedVar x = Compose (Sized (sizedFVedVarSize' x) (FVed (sizedFVedVarFreeVars' x) x))

sizedFVedValue :: SizedFVedValue -> (Compose Sized FVed) SizedFVedValue
sizedFVedValue v = Compose (Sized (sizedFVedValueSize' v) (FVed (sizedFVedValueFreeVars' v) v))

sizedFVedTerm :: TermF (Compose Sized FVed) -> SizedFVedTerm
sizedFVedTerm e = Compose (Sized (sizedFVedTermSize' e) (FVed (sizedFVedTermFreeVars' e) e))
