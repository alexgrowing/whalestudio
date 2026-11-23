import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceModel

def DescendsTo {R₀ R : Type} [CommRing R₀] [CommRing R] (ic : R₀ →+* R) (j : R →+* Qb) {G₀ H₀ : Over (Sp R₀)}
    [GrpObj G₀] [GrpObj H₀] {GQ HQ : Over (Sp Qb)} [GrpObj GQ] [GrpObj HQ] (gQ : GQ.left ⟶ G₀.left)
    (hQ : HQ.left ⟶ H₀.left) (f : GQ ⟶ HQ) : Prop :=
  ∀ (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (g : G.left ⟶ G₀.left) (h : H.left ⟶ H₀.left) (pG : GQ.left ⟶ G.left)
    (pH : HQ.left ⟶ H.left), IsGrpPullback G G₀ (spMap ic) g → IsGrpPullback H H₀ (spMap ic) h →
    IsGrpPullback GQ G (spMap j) pG → IsGrpPullback HQ H (spMap j) pH → pG ≫ g = gQ → pH ≫ h = hQ →
    ∃ F : G ⟶ H, f.left ≫ pH = pG ≫ F.left

end GlobalTheory.PlaceModel
