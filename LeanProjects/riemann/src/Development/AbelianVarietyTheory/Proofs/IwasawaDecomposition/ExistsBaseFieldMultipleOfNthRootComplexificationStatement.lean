import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseFieldMultipleOfNthRootComplexification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_field_multiple_of_nth_root_complexification : ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A] [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 → w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  first | exact @GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul | exact GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul | (intros; apply GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul <;> assumption)
