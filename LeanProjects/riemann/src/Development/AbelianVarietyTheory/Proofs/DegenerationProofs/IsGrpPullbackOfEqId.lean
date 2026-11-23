import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.SelfCmp

theorem isGrpPullback_of_eq_id {S : Scheme.{0}} (G : Over S) [GrpObj G] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback G G f (𝟙 G.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem isCPMap_of_eq_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {f : S ⟶ S}
    (hf : f = 𝟙 S) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ f) : IsCPMap P P f (𝟙 G.left) hw (GlobalTheory.UU.idIso P.L.L) := by
  subst hf
  exact IsCPMap.id P

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

def selfCmp {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) :
    Cmp (RingHom.id R) U U (𝟙 _) where
  pb := isGrpPullback_of_eq_id G (spMap_id R)
  wL := GlobalTheory.UU.idIso _
  wL_map := isCPMap_of_eq_id U.P (spMap_id R) _
  β := 𝟙 _
  pbB := isGrpPullback_of_eq_id D.P.A (spMap_id R)
  v := GlobalTheory.UU.idIso _
  v_gen := GlobalTheory.UU.idIso_isGen D.P.isLB
  xe := AddEquiv.refl _
  c_pr x := by
    rw [spMap_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  lev e Z x' x h := by
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : Mono (fstG I e G).left := inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))
    rw [Category.comp_id] at h
    obtain rfl : x = x' := (cancel_mono _).1 h
    refine ⟨by rw [Category.comp_id], fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
    · refine (val_change ((U.gt e).t_gen χ) x hJ hJ').trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl ?_))
      refine Finset.prod_congr rfl fun k _ => congrArg (· ^ Oinvε k) ?_
      rw [Category.comp_id]
      exact (gw_idIso _ _ _ (hJ _) (hJ' _)).symm
    · have a := (isGen_iff _).1 (U.w_gen e) Z x z (J (x ≫ (U.gt e).pG.left)) (J' (x ≫ (U.gt e).pG.left))
        (fun _ => k) (fun _ => k') (hJ _) (hJ' _) (mem_pull.2 hk) (mem_pull.2 hk')
      have b := gm_pull_g U.P.L.L (fstG I e G).left x z (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
      rw [gw_idIso _ _ _ (hJ _) (hJ' _), gw_idIso _ (x ≫ (fstG I e G).left) z hk hk', a, b, mul_right_comm,
        inv_mul_cancel_right]

end GlobalTheory.LN.SelfCmp
end
