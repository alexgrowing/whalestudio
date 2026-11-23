import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_weight_square_length_lt : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L : List (ASeg T)) (n : Multiset (ASeg T)), AOrdered s L → InSh s n (wt s L) → n ≠ (L : Multiset (ASeg T)) → sqLen n < sqLen (L : Multiset (ASeg T)) := by
  first | exact @GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh | exact GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh | (intros; apply GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh <;> assumption)
