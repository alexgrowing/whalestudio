import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLogPushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_log_pushforward : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Tw Z), T.LnPush := by
  first | exact @GlobalTheory.ShFam.GalCarry.LnPushProof.lnPush | exact GlobalTheory.ShFam.GalCarry.LnPushProof.lnPush | (intros; apply GlobalTheory.ShFam.GalCarry.LnPushProof.lnPush <;> assumption)
