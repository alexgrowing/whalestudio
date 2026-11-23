import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLtStatement

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegmentWords

theorem wt_inSh_antisymm : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L →
    AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) →
    InSh s (L : Multiset (ASeg T)) (wt s M) →
    (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  intro T s hs hj L M hL hM hLM hML
  by_contra hne
  have h1 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj L (M : Multiset (ASeg T)) hL hLM (Ne.symm hne)
  have h2 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj M (L : Multiset (ASeg T)) hM hML hne
  exact lt_asymm h1 h2

end GlobalTheory.CompanionTheory.SegmentWords
