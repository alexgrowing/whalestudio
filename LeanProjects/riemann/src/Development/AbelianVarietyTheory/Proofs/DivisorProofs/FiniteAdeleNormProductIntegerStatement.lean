import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleNormProductInteger
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_norm_product_integer : ∀ (F : Type) [Field F] [NumberField F] (c : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v), (∀ v, c v ≠ 0) → (∀ v, ‖c v‖₊ ≤ 1) →
    (Function.mulSupport fun v => ‖c v‖₊).Finite →
    ∃ m : ℕ, 0 < m ∧ (∏ᶠ v, ‖c v‖₊) = (m : ℝ≥0)⁻¹ ∧ ∀ v, ‖(m : Fv F v)‖₊ ≤ ‖c v‖₊ := by
  first | exact @GlobalTheory.exists_nat_finprod_nnnorm_eq_inv | exact GlobalTheory.exists_nat_finprod_nnnorm_eq_inv | (intros; apply GlobalTheory.exists_nat_finprod_nnnorm_eq_inv <;> assumption)
