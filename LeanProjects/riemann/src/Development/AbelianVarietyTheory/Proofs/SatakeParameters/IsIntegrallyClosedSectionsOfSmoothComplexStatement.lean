import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegrallyClosedSectionsOfSmoothComplex
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  first | (exact @GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (exact GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (intros; apply GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex  <;> assumption)
