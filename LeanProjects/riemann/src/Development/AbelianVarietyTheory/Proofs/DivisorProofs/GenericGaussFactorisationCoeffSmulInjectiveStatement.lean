import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGaussFactorisationCoeffSmulInjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericGaussFactorisation_coeff_smul_injective : ∀ (O : Type) [CommRing O] (N : ℕ) (M : Type) [AddCommGroup M] [Module O M] (s : Finset (Fin N × Fin N →₀ ℕ)) (c : (Fin N × Fin N →₀ ℕ) → M), (∀ n, ∑ m ∈ s, (lduHom O N (monomial m 1)).coeff n • c m = 0) → ∀ m ∈ s, c m = 0 := by
  first | exact @GlobalTheory.GenCoef.lduHom_coeff_smul_injective | exact GlobalTheory.GenCoef.lduHom_coeff_smul_injective | (intros; apply GlobalTheory.GenCoef.lduHom_coeff_smul_injective <;> assumption)
