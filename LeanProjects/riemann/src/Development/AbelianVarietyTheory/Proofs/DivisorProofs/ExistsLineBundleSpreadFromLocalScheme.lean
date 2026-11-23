import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleNhdOfStalkBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNhdOfStalkBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SpreadLB

open GlobalTheory.CechPic in
theorem exists_spread : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] (f : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] (j : U ⟶ S) [IsOpenImmersion j] (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (L : LB YU), L.IsLB → ∀ (x : S) (N : LB (pullback f (S.fromSpecStalk x))), N.IsLB → (∀ (T : Scheme.{0}) (a : T ⟶ pullback f (S.fromSpecStalk x)) (b : T ⟶ YU), a ≫ pullback.fst f (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(f ⁻¹ᵁ W), N'.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N'.pull a) (L.pull b) := by

  intro S Y U YU _ f _ _ j _ e fU hpb L hL x N hN hag
  obtain ⟨W₁, hx₁, N₁, hN₁, hq⟩ := GlobalTheory.T.exists_lineBundle_nhd_of_stalk_baseChange f x N hN
  have hr1 : Set.range (pullback.fst f (S.fromSpecStalk x)) ⊆ Set.range (f ⁻¹ᵁ W₁).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show f (pullback.fst f (S.fromSpecStalk x) y) ∈ W₁
    have hsp : f (pullback.fst f (S.fromSpecStalk x) y) ⤳ x := by
      have : f (pullback.fst f (S.fromSpecStalk x) y) ∈ Set.range (S.fromSpecStalk x) :=
        ⟨pullback.snd f (S.fromSpecStalk x) y, by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact hsp.mem_open W₁.isOpen hx₁
  let q₁ := IsOpenImmersion.lift (f ⁻¹ᵁ W₁).ι (pullback.fst f (S.fromSpecStalk x)) hr1
  have hq₁ : q₁ ≫ (f ⁻¹ᵁ W₁).ι = pullback.fst f (S.fromSpecStalk x) := IsOpenImmersion.lift_fac _ _ _
  have iso1 := hq q₁ hq₁
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip inferInstance
  haveI : QuasiCompact e := MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip inferInstance
  haveI : QuasiCompact (f ⁻¹ᵁ W₁).ι := MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_morphismRestrict f W₁) inferInstance
  let h : pullback (f ⁻¹ᵁ W₁).ι e ⟶ S := pullback.fst (f ⁻¹ᵁ W₁).ι e ≫ (f ⁻¹ᵁ W₁).ι ≫ f

  obtain ⟨W₂, hx₂, iso2⟩ := GlobalTheory.T.exists_lineBundleIso_nhd_of_stalk_baseChange h x (N₁.pull (pullback.fst (f ⁻¹ᵁ W₁).ι e))
    (L.pull (pullback.snd (f ⁻¹ᵁ W₁).ι e)) (pull_isLB hN₁ _) (pull_isLB hL _) (by
      set r := pullback.fst h (S.fromSpecStalk x)
      have hs : (r ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e ≫ (f ⁻¹ᵁ W₁).ι) ≫ f = pullback.snd h (S.fromSpecStalk x) ≫ S.fromSpecStalk x := by
        rw [← pullback.condition]; simp only [h, Category.assoc]; rfl
      let s := pullback.lift _ _ hs
      have hs1 : s ≫ q₁ = r ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e := by
        rw [← cancel_mono (f ⁻¹ᵁ W₁).ι, Category.assoc, hq₁]; simp only [s, pullback.lift_fst, Category.assoc]
      have hs2 : s ≫ pullback.fst f (S.fromSpecStalk x) = (r ≫ pullback.snd (f ⁻¹ᵁ W₁).ι e) ≫ e := by
        simp only [s, pullback.lift_fst, Category.assoc, pullback.condition]
      have i3 := (cls_eq_iff (pull_isLB hN _) (pull_isLB hL _)).2 (hag _ s _ hs2)
      have i1 := (cls_eq_iff (pull_isLB hN₁ _) hN).2 iso1
      refine (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) r) (pull_isLB (pull_isLB hL _) r)).1 ?_
      rw [cls_pull (pull_isLB hN₁ _), cls_pull hN₁, cls_pull (pull_isLB hL _), cls_pull hL, ← pull_comp, ← pull_comp, ← hs1,
        pull_comp, ← cls_pull hN₁ _ (pull_isLB hN₁ _), i1, ← cls_pull hN _ (pull_isLB hN _), i3, cls_pull hL])
  refine ⟨W₁ ⊓ W₂, ⟨hx₁, hx₂⟩, ?_⟩
  have hle : f ⁻¹ᵁ (W₁ ⊓ W₂) ≤ f ⁻¹ᵁ W₁ := fun y hy => hy.1
  refine ⟨N₁.pull (Y.homOfLE hle), pull_isLB hN₁ _, fun T a b hab => ?_⟩
  have hc : (a ≫ Y.homOfLE hle) ≫ (f ⁻¹ᵁ W₁).ι = b ≫ e := by rw [Category.assoc, Scheme.homOfLE_ι, hab]
  let c := pullback.lift _ _ hc
  have hcr : Set.range c ⊆ Set.range (h ⁻¹ᵁ W₂).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (c t) ∈ W₂
    have : c ≫ h = a ≫ (f ⁻¹ᵁ (W₁ ⊓ W₂)).ι ≫ f := by
      simp only [h, c, pullback.lift_fst_assoc, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
    exact ((a t).2 : _).2
  let d := IsOpenImmersion.lift (h ⁻¹ᵁ W₂).ι c hcr
  have hd : d ≫ (h ⁻¹ᵁ W₂).ι = c := IsOpenImmersion.lift_fac _ _ _
  have i2 := (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) _) (pull_isLB (pull_isLB hL _) _)).2 iso2
  refine (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) a) (pull_isLB hL b)).1 ?_
  have e1 : a ≫ Y.homOfLE hle = d ≫ (h ⁻¹ᵁ W₂).ι ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e := by
    rw [← Category.assoc, hd]; simp only [c, pullback.lift_fst]
  have e2 : b = d ≫ (h ⁻¹ᵁ W₂).ι ≫ pullback.snd (f ⁻¹ᵁ W₁).ι e := by
    rw [← Category.assoc, hd]; simp only [c, pullback.lift_snd]
  rw [cls_pull (pull_isLB hN₁ _), cls_pull hN₁, ← pull_comp, e1, cls_pull hL, e2, pull_comp, pull_comp, pull_comp d,
    pull_comp (h ⁻¹ᵁ W₂).ι, ← cls_pull hN₁ _ (pull_isLB hN₁ _), ← cls_pull (pull_isLB hN₁ _) _ (pull_isLB (pull_isLB hN₁ _) _), i2,
    cls_pull (pull_isLB hL _), cls_pull hL]

end GlobalTheory.SpreadLB
