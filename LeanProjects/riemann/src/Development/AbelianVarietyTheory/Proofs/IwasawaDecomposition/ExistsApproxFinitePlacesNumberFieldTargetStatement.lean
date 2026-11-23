import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldTarget
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_finite_places_numberField_target : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ), ∃ a : F, ∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ)) := by
  first | exact @GlobalTheory.FinPlaceApprox.approx_target | exact GlobalTheory.FinPlaceApprox.approx_target | (intros; apply GlobalTheory.FinPlaceApprox.approx_target <;> assumption)
