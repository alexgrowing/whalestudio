import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonSemiAbelianPullbackTwoUnitaryTraits
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_semiAbelian_pullback_two_unitary_traits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∃ tW : SAB H (Sp W), Nonempty (SABMap tW T.t (spMap f)) ∧ Nonempty (SABMap tW T'.t (spMap f')) := by
  first | exact @GlobalTheory.UPoinc.TraitUniq.exists_common_pull | exact GlobalTheory.UPoinc.TraitUniq.exists_common_pull | (intros; apply GlobalTheory.UPoinc.TraitUniq.exists_common_pull <;> assumption)
