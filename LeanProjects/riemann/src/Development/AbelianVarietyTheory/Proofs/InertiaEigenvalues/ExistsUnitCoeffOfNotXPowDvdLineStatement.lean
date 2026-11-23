import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffOfNotXPowDvdLine
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_coeff_of_not_X_pow_dvd_line : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [Algebra (X.O0 i) K], IsRes i K → ∀ (b : ι → K) (n : ℕ), n ≤ X.l i ^ M → ∀ F G : MvPolynomial ι (X.O0 i), toLam X i M ι F = toLam X i M ι G → ¬ (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) G → ∃ m : ι →₀ ℕ, m.degree < n ∧ IsUnit (F.coeff m) := by
  first | exact @GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line | exact GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line | (intros; apply GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line <;> assumption)
