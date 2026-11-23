import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferential
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_sub_subst_integral_of_integral_differential : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, Red p (u i) (w i)) → (∀ i, Red p (v i) (w i)) → f ∈ quasiInt p k σ → subst u f - subst v f ∈ intBy p k τ p := by
  first | exact @GlobalTheory.Katz.subst_sub_subst_mem_intBy | exact GlobalTheory.Katz.subst_sub_subst_mem_intBy | (intros; apply GlobalTheory.Katz.subst_sub_subst_mem_intBy <;> assumption)
