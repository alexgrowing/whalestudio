import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTrait
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_uniformisation_pulled_back_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  first | exact @GlobalTheory.UPoinc.TraitPull.exists_pull_unif | exact GlobalTheory.UPoinc.TraitPull.exists_pull_unif | (intros; apply GlobalTheory.UPoinc.TraitPull.exists_pull_unif <;> assumption)
