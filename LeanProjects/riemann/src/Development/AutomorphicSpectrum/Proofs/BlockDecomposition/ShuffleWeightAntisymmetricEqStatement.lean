import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightAntisymmetricEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_weight_antisymmetric_eq : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L → AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) → InSh s (L : Multiset (ASeg T)) (wt s M) → (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  first | exact @GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm | exact GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm | (intros; apply GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm <;> assumption)
