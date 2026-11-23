import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfAffineHyperplaneLineSums
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_affineHyperplane_line_sums : ∀ (k W M : Type) [Field k] [Fintype k] [DecidableEq k] [AddCommGroup W] [Module k W] [Finite W] [AddCommGroup M] [Module ℂ M] (ψ : W → M), ψ 0 = 0 → (∀ g : Module.Dual k W, g ≠ 0 → ∑ᶠ x ∈ {x | g x = 1}, ψ x = 0) → (∀ x, ∑ a : kˣ, ψ ((a : k) • x) = 0) → ∀ x, ψ x = 0 := by
  first | exact @GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums | exact GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums | (intros; apply GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums <;> assumption)
