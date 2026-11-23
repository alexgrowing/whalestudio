import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordOfIsPullDegId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsProduct
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PelUnifUniqCoord

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → ∀ (t : SAB H (Sp W)) (P P' : PELUnif (maximalIdeal W) t),
      ∃ e : P.D.toPre.X ≃ₗ[𝓞 E] P'.D.toPre.X, ∀ y r r', PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (e y) r' →
        Associated (r ^ 2) (r' ^ 2) := by
  intro E _ _ _ H W _ _ _ hW t P P'
  haveI : CharZero W := hW.2
  obtain ⟨m, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨e, he⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H W t t m P P' hW.1.1 hW.1.2.2.1 hW.1.2.2.2
  refine ⟨e, fun y r r' hr hr' => ?_⟩
  obtain ⟨u, hu⟩ := he y r hr
  have h1 : Associated (u * r) r' := GlobalTheory.TorRef.psiCoord_associated hu hr'
  have h2 : Associated r r' := (associated_unit_mul_left r u u.isUnit).symm.trans h1
  exact h2.pow_pow

end GlobalTheory.PelUnifUniqCoord
