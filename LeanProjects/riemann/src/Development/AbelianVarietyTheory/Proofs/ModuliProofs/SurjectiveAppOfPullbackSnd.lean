import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppTopPullbackSndOfApp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RigidLocal

open GlobalTheory.CechPic

private theorem surjective_app_of_eq_of_surjective_comp_injective {X S : Scheme.{0}} (f : X ⟶ S) {W V : S.Opens} (e : W = V)
    {R : CommRingCat} (g : Γ(X, f ⁻¹ᵁ W) ⟶ R)
    (h : Function.Surjective (f.app W ≫ g).hom) (hg : Function.Injective g.hom) :
    Function.Surjective (f.app V).hom := by
  subst e
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h.of_comp_left hg

theorem surjective_app_of_pullback_snd {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : Function.Surjective (pullback.snd f V.ι).appTop.hom) : Function.Surjective (f.app V).hom := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.coe_comp] at h
  have hi : IsIso (pullbackRestrictIsoRestrict f V).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))
  have h2 : Function.Surjective (f ∣_ V).appTop.hom :=
    h.of_comp_left (ConcreteCategory.bijective_of_isIso (pullbackRestrictIsoRestrict f V).hom.appTop).1
  rw [morphismRestrict_appTop] at h2
  refine surjective_app_of_eq_of_surjective_comp_injective f V.ι_image_top _ h2 ?_
  exact (ConcreteCategory.bijective_of_isIso
    (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f V ⊤)).op).hom).1

theorem eSec_comp {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] {φ : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (𝟙 S) φ) : eSec A ≫ φ = eSec A' :=
  (GlobalTheory.PolBaseChange.eSec_comm h).trans (Category.id_comp _)

theorem lbIso_of_local : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (φ : A.left ⟶ A'.left), IsAbelianScheme A → L.IsLB → L'.IsLB → Out.Rigidified A L → Out.Rigidified A' L' → IsGrpPullback A A' (𝟙 S) φ → (∀ p : S, ∃ (V B : Scheme.{0}) (x : V ⟶ S) (q : B ⟶ V) (a : B ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsPullback a q A.hom x ∧ LBIso (L.pull a) (L'.pull (a ≫ φ))) → LBIso L (L'.pull φ) := by
  intro hG S A A' _ _ L L' φ hA hL hL' hR hR' hφ hloc
  have hM : (L'.pull φ).IsLB := LB.isLB_pull hL' φ
  have hN : (LB.div L (L'.pull φ)).IsLB := LB.isLB_div hL hM

  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ A.left),
      (∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull g), t.IsGen) ↔
        CechPic.pull g (CechPic.cls L hL) = CechPic.pull g (CechPic.cls _ hM) := by
    intro Y g
    rw [← cls_eq_zero_iff (LB.isLB_pull hN g), cls_pull hN g (LB.isLB_pull hN g), cls_div hL hM hN,
      map_sub, sub_eq_zero]

  have hsec : ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (eSec A)), t.IsGen := by
    rw [key]
    have h1 : CechPic.pull (eSec A) (CechPic.cls L hL) = 0 := by
      rw [← cls_pull hL (eSec A) (LB.isLB_pull hL _)]
      exact (cls_eq_zero_iff _).2 hR
    have h2 : CechPic.pull (eSec A') (CechPic.cls L' hL') = 0 := by
      rw [← cls_pull hL' (eSec A') (LB.isLB_pull hL' _)]
      exact (cls_eq_zero_iff _).2 hR'
    rw [h1, cls_pull hL' φ hM, ← pull_comp, eSec_comp hφ, h2]

  have hloc' : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen ((LB.div L (L'.pull φ)).pull (A.hom ⁻¹ᵁ U).ι), t.IsGen := by
    intro s
    obtain ⟨V, B, x, q, a, hx, hs, hpb, hiso⟩ := hloc s
    refine ⟨x.opensRange, hs, ?_⟩
    rw [key]
    have w : (A.hom ⁻¹ᵁ x.opensRange).ι ≫ A.hom = ((A.hom ∣_ x.opensRange) ≫ x.isoOpensRange.inv) ≫ x := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
    obtain ⟨e, he⟩ : ∃ e, e ≫ a = (A.hom ⁻¹ᵁ x.opensRange).ι := ⟨hpb.lift _ _ w, hpb.lift_fst _ _ w⟩
    have ha : CechPic.pull a (CechPic.cls L hL) = CechPic.pull a (CechPic.cls _ hM) := by
      have h := (cls_eq_iff (LB.isLB_pull hL a) (LB.isLB_pull hL' (a ≫ φ))).2 hiso
      rw [cls_pull hL a, cls_pull hL' (a ≫ φ), pull_comp] at h
      rw [h, cls_pull hL' φ hM]
    rw [← he, pull_comp, pull_comp, ha]
  have hσ : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    exact (Over.w _).trans rfl
  have hsurj : ∀ U : S.Opens, Function.Surjective (A.hom.app U).hom := fun U =>
    surjective_app_of_pullback_snd A.hom U (surj_snd hG hA (Over.mk U.ι))
  obtain ⟨t, ht⟩ := exists_gen_of_local_of_section A.left S A.hom (eSec A) _ hN hσ hsurj hloc' hsec
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 ((cls_div hL hM hN).symm.trans ((cls_eq_zero_iff hN).2 ⟨t, ht⟩)))

end GlobalTheory.RigidLocal
