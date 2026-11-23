import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationAtUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatTrivSec

variable {X Y : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

def pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) : LB.Sec (L.pull F) where
  f := fun I => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : PUnit => F) I PUnit.unit)).op).hom
    ((F.app _).hom (θ.f (I PUnit.unit)))
  compat := fun I J => fn_ext fun y hy => by
    have hI : F y ∈ L.U (I PUnit.unit) := mem_pull.1 hy.1
    have hJ : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.2
    have hm : (𝟙 Y ≫ F) y ∈ L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit) := ⟨hI, hJ⟩
    refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.1 _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_))
    refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 Y) y I J hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.2 _).trans (gs_pull (𝟙 Y) F y _ hJ _))))).symm
    exact (gs_res _ y inf_le_left hm _).symm.trans ((congrArg (gs _ y _) (θ.compat _ _)).trans
      ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))

theorem gs_pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) (y : Y) (J : PUnit → L.ι) (hy : y ∈ (L.pull F).U J) :
    gs (𝟙 Y) y _ ((pullSec L θ F).f J) = gs F y (L.U (J PUnit.unit)) (θ.f (J PUnit.unit)) := by
  have hI : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy
  refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_)
  rw [Category.id_comp]

theorem cst_bijective_of {C : Type} [CommRing C] (V : (Sp C).Opens)
    (hV : Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) :
    Function.Bijective (cst V.ι ⊤) := by
  have key : ∀ (V' : (Sp C).Opens) (h : V' ≤ ⊤), V' = V →
      Function.Bijective ((Sp C).presheaf.map (homOfLE h).op).hom := by
    rintro V' h rfl
    exact hV
  have h₁ : Function.Bijective V.ι.appTop.hom := by
    rw [Scheme.Opens.ι_appTop]
    exact key _ _ V.ι_image_top
  have h₀ : Function.Bijective (rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) := by
    have : ⇑(rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) = id := funext fun x => rs_self _ x
    rw [this]
    exact Function.bijective_id
  have h₃ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  exact h₀.comp (h₁.comp h₃)

theorem gs_cst_top {C : Type} [CommRing C] {Z : Scheme.{0}} (f : Z ⟶ Sp C) (z : Z) (x : C) :
    gs (𝟙 Z) z ⊤ (cst f ⊤ x) = gs f z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom x) := by
  refine (gs_res (𝟙 Z) z (U := f ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _).trans ((gs_pull (𝟙 Z) f z ⊤ trivial _).trans ?_)
  rw [Category.id_comp]

theorem exists_sec_near : ∀ (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] (g : B →+* C), g.Flat → ∀ (W : (Sp B).Opens), Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : spMap g ⁻¹ᵁ W ≤ ⊤)).op).hom → ∀ (M : LB W.toScheme), M.IsLB → Triv (M.pull (spMap g ∣_ W)) → ∀ y : Sp C, ∃ (s : M.Sec) (D : (Sp C).Opens), y ∈ D ∧ ∀ z : (spMap g ⁻¹ᵁ W).toScheme, (spMap g ⁻¹ᵁ W).ι z ∈ D → (spMap g ∣_ W) z ∈ Out.nonzeroLocus s := by
  intro B C _ _ _ g hg W hbij M hM hT y
  classical
  haveI : CompactSpace W.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (W : Set (Sp B)))
  obtain ⟨t, ht⟩ := hT
  obtain ⟨n, c, u, hcomb⟩ := FlatSec.exists_comb_of_flat B C g hg W.toScheme W.ι _ (spMap g ∣_ W)
    (spMap g ⁻¹ᵁ W).ι (isPullback_morphismRestrict (spMap g) W) M hM (genSec t ht)
  choose a ha using fun i => DVR.ValuationAtUnit.exists_glue_ratio
    (DVR.linComb_cover M hM (fun _ : PUnit => spMap g ∣_ W) (fun _ => 1)) (pullSec M (u i) (spMap g ∣_ W)) t ht
  have hb := cst_bijective_of _ hbij
  choose e he using fun i => hb.2 (a i)
  have chart : ∀ z : (spMap g ⁻¹ᵁ W).toScheme, ∃ k, (spMap g ∣_ W) z ∈ M.U k := fun z => by
    have hz : (spMap g ∣_ W) z ∈ ⨆ k, M.U k := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hz
  have key : ∀ (z : (spMap g ⁻¹ᵁ W).toScheme) (k : M.ι), (spMap g ∣_ W) z ∈ M.U k → ∀ i,
      gs (spMap g ∣_ W) z _ ((u i).f k) = gs (𝟙 _) z ⊤ (a i) * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
    intro z k hk i
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    refine (gs_pullSec M (u i) _ z (fun _ => k) hz).symm.trans ?_
    refine (congrArg (gs (𝟙 _) z _) (ha i (fun _ => k))).trans ?_
    rw [gs_mul (𝟙 _) z _ hz, gs_res (𝟙 _) z _ hz, gs_unit (𝟙 _) z _ hz]
  have hsum : ∑ i, c i * e i = 1 := by
    apply hb.1
    rw [map_sum, map_one]
    refine fn_ext fun z _ => ?_
    obtain ⟨k, hk⟩ := chart z
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    have h1 := hcomb z k hk
    simp only [key z k hk] at h1
    have h2 : gs (𝟙 _) z _ ((genSec t ht).f (fun _ => k)) = (gm (𝟙 _) z _ (t.s (fun _ => k))).val :=
      gs_unit (𝟙 _) z _ hz _
    rw [h2] at h1
    simp only [map_mul, he]
    rw [FlatSec.gs_sum (𝟙 _) z ⊤ trivial, gs_eq (𝟙 _) z ⊤ trivial 1, map_one, map_one]
    simp only [gs_mul (𝟙 _) z ⊤ trivial]
    have h3 : (∑ i, gs (𝟙 _) z ⊤ (cst (spMap g ⁻¹ᵁ W).ι ⊤ (c i)) * gs (𝟙 _) z ⊤ (a i)) *
        (gm (𝟙 _) z _ (t.s (fun _ => k))).val = 1 * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
      rw [_root_.one_mul, Finset.sum_mul]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_assoc _ _ _) h1.symm
    exact (Units.mul_left_inj _).1 h3
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ y.asIdeal := by
    by_contra hne
    push_neg at hne
    apply y.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hne i)
  refine ⟨u i, PrimeSpectrum.basicOpen (e i), hi, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := chart z
  have hu1 : IsUnit (gs (𝟙 _) z ⊤ (a i)) := by
    rw [← he i, gs_cst_top, isUnit_gs_iff _ z ⊤ trivial, basicOpen_eq_of_affine]
    exact hz
  have hu2 : IsUnit (gs (spMap g ∣_ W) z _ ((u i).f k)) := by
    rw [key z k hk i]
    exact hu1.mul (Units.isUnit _)
  rw [isUnit_gs_iff _ z _ hk] at hu2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hu2⟩

end GlobalTheory.FlatTrivSec
