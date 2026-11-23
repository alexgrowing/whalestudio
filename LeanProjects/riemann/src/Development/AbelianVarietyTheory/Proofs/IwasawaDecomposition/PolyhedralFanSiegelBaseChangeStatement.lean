import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyhedralFanSiegelBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyhedral_fan_siegel_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (φ φs : InvFun ℤ) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F), 1 ≤ D.p + D.q → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → SiegAt (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n → 3 ≤ n → Odd n → n ∣ l.M → AgreesPsd (Module.finrank ℚ E / 2 * (D.p + D.q)) φs φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → ∃ C : Model Xo c ω, HasCones (ConeZ E φs) C ∧ PolRay (comb 0 (resInt _ φs) 0 (resInt _ φs)) (resInt _ φs) 1 C := by
  first | exact @GlobalTheory.SiegLoc.exists_siegel_model | exact GlobalTheory.SiegLoc.exists_siegel_model | (intros; apply GlobalTheory.SiegLoc.exists_siegel_model <;> assumption)
