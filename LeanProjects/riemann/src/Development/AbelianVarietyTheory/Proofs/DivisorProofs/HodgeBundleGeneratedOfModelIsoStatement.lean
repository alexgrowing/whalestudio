import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_bundle_generated_of_model_iso : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (R : Type) [CommRing R] (ω : R →+* c.F) (Y C : Model Xo c ω) (g N : ℕ), IsDedFrac ω → GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) g → GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega C.t.G) g → IsGenerated (lbPow (hodge C.t.G g) N) → IsGenerated (lbPow (hodge Y.t.G g) N) := by
  first | exact @GlobalTheory.HodgeGenDesc.main | exact GlobalTheory.HodgeGenDesc.main | (intros; apply GlobalTheory.HodgeGenDesc.main <;> assumption)
