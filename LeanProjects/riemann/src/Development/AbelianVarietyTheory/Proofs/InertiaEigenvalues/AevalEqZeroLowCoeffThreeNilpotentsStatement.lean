import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroLowCoeffThreeNilpotents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_low_coeff_three_nilpotents : ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ) (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 → (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) → (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) → MvPolynomial.aeval ξ F = 0 := by
  first | exact @GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent | exact GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent | (intros; apply GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent <;> assumption)
