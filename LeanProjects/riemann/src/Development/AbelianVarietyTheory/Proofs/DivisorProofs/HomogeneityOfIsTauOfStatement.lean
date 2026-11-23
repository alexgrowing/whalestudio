import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf L c τ → (∀ z, c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice) ∧ (∀ z, L.weierstrassP (c * z) = (c ^ 2)⁻¹ * (tauPair τ).weierstrassP z) ∧ (∀ z, L.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * (tauPair τ).derivWeierstrassP z) ∧ s2 L = (c ^ 2)⁻¹ * s2 (tauPair τ) ∧ area L = ‖c‖ ^ 2 * area (tauPair τ) := by
  first | exact @GlobalTheory.WpFam.homogeneity_of_isTauOf | exact GlobalTheory.WpFam.homogeneity_of_isTauOf | (intros; apply GlobalTheory.WpFam.homogeneity_of_isTauOf <;> assumption)
