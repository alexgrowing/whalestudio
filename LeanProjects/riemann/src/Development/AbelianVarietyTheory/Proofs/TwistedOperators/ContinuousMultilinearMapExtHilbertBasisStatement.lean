import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMultilinearMapExtHilbertBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitHeightSummableExpNegAbs
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F), (∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) → f = g := by
  first | exact @GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | exact GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | (intros; apply GlobalTheory.continuousMultilinearMap_ext_hilbertBasis <;> assumption)
