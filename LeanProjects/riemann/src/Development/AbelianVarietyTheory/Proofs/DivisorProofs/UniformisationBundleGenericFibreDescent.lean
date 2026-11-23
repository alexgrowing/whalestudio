import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory

namespace GenericBundleDescent

variable {X X' Y Z : Scheme.{0}}

theorem pull_both {M : LB X} {N : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'} (H : LBIso (M.pull a) (N.pull b)) (h : Z ⟶ Y)
    {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = h ≫ a) (eb : b' = h ≫ b) : LBIso (M.pull a') (N.pull b') :=
  LBIso.chartPull (chartPullSame M _ _ _ h fun _ => ea) (chartPullSame N _ _ _ h fun _ => eb) H

theorem pull_right {M : LB Y} {N : LB X'} {b : Y ⟶ X'} (H : LBIso M (N.pull b)) (h : Z ⟶ Y)
    {b' : Z ⟶ X'} (eb : b' = h ≫ b) : LBIso (M.pull h) (N.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M h h rfl) (chartPullSame N _ _ _ h fun _ => eb) H

theorem pull_pull {M : LB X} {N : LB Z} {a : Y ⟶ X} {h : Z ⟶ Y} (H : LBIso (M.pull (h ≫ a)) N) :
    LBIso ((M.pull a).pull h) N :=
  LBIso.chartPull (chartPullLinComb M a (fun _ : PUnit => h) (fun _ => h ≫ a) (fun _ => 1) (𝟙 Z)
    fun _ => (Category.id_comp _).symm) (chartPullId N) H

theorem mono_jK (R : Type) [CommRing R] : Mono (jK R) := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  infer_instance

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GenericBundleDescent

open GenericBundleDescent in

theorem unif_bundle_generic_descent : ∀ (R W R₂ W₂ K' Ω' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] [Field K'] [Field Ω'] (φ : R →+* W) (ρ : R →+* R₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (io : FractionRing R →+* K') (j : FractionRing W →+* Ω') (l : K' →+* Ω') (i : K' ≃+* FractionRing R₂) (j₂ : FractionRing W₂ →+* Ω'), Function.Injective φ → Function.Injective ρ → Function.Injective σ → Function.Injective φ₂ → φ₂.comp ρ = σ.comp φ → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) → (∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r))) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (α : AW.A.left ⟶ A.A.left), IsGrpPullback GW G (spMap φ) βW → UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (p : pullback AW.A.hom (spMap j) ⟶ A₁.A.left), IsGrpPullback A₁.A A.A (spMap io) α₁ → p ≫ α₁ = pullback.fst _ _ ≫ α → p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l → LBIso (AW.L.pull (pullback.fst AW.A.hom (spMap j))) (A₁.L.pull p) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsGrpPullback G₂ G (spMap ρ) β → IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q → LBIso A₂.L (A₁.L.pull q) → gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (GW' : Over (Sp W₂)) [GrpObj GW'] [IsCommMonObj GW'] (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' → IsGrpPullback GW' GW (spMap σ) τ → βW' ≫ β = τ ≫ βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R W R₂ W₂ K' Ω' _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ρ σ φ₂ io j l i j₂ _ _ _ _ _ _ _ hj₂σ hj₂φ G _ _ A gen GW _ _ βW DW
    AW UW α _ hα A₁ α₁ p hA₁ hp₁ hp₂ hLp G₂ _ _ β A₂ gen₂ q _ hq hLq hgq GW' _ _ βW' τ DW' AW' UW' κ hβW' hτ hsq hκ hL
  have := mono_jK R
  have := mono_jK R₂
  let π := pullback.fst (pullback.snd GW'.hom (jK W₂)) (spMap j₂)
  let s := pullback.snd (pullback.snd GW'.hom (jK W₂)) (spMap j₂)
  have hπ : π ≫ pullback.fst GW'.hom (jK W₂) ≫ GW'.hom = s ≫ spMap j₂ ≫ jK W₂ := by
    rw [pullback.condition, pullback.condition_assoc]
  have e₁ : spMap j₂ ≫ jK W₂ ≫ spMap σ = spMap j ≫ jK W := by
    rw [sp_comp, sp_comp, sp_comp]
    exact congrArg spMap (RingHom.ext hj₂σ)
  have e₂ : spMap j₂ ≫ jK W₂ ≫ spMap φ₂ = spMap (l.comp i.symm.toRingHom) ≫ jK R₂ := by
    rw [sp_comp, sp_comp, sp_comp]
    exact congrArg spMap (RingHom.ext hj₂φ)
  have e₃ : spMap (l.comp i.symm.toRingHom) ≫ spMap i.toRingHom = spMap l := by
    rw [sp_comp]
    exact congrArg spMap (RingHom.ext fun x => by simp)
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ : ∃ ℓ : _ ⟶ pullback GW.hom (jK W),
      ℓ ≫ pullback.fst _ _ = π ≫ pullback.fst GW'.hom (jK W₂) ≫ τ ∧ ℓ ≫ pullback.snd _ _ = s ≫ spMap j :=
    ⟨pullback.lift _ _ (by
      rw [Category.assoc, Category.assoc, hτ.1.w, reassoc_of% hπ, e₁, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have wW : UW.gen.hom.left ≫ AW.A.hom = pullback.snd GW.hom (jK W) := Over.w UW.gen.hom
  have w₂ : gen₂.hom.left ≫ A₂.A.hom = pullback.snd G₂.hom (jK R₂) := Over.w gen₂.hom
  let gW : pullback GW.hom (jK W) ⟶ AW.A.left := UW.gen.hom.left
  let g₂ : pullback G₂.hom (jK R₂) ⟶ A₂.A.left := gen₂.hom.left
  let gi : A.A.left ⟶ pullback G.hom (jK R) := gen.inv.left
  have wW' : gW ≫ AW.A.hom = pullback.snd GW.hom (jK W) := wW
  have w₂' : g₂ ≫ A₂.A.hom = pullback.snd G₂.hom (jK R₂) := w₂
  have hα' : gW ≫ α ≫ gi ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := by
    have c : UW.gen.hom.left ≫ UW.gen.inv.left = 𝟙 _ := congrArg Over.Hom.left UW.gen.hom_inv_id
    exact (congrArg (UW.gen.hom.left ≫ ·) hα.symm).trans (by rw [reassoc_of% c])
  have hgq' : g₂ ≫ q ≫ α₁ ≫ gi ≫ pullback.fst G.hom (jK R) = pullback.fst G₂.hom (jK R₂) ≫ β := by
    have c : gen₂.hom.left ≫ gen₂.inv.left = 𝟙 _ := congrArg Over.Hom.left gen₂.hom_inv_id
    exact (congrArg (gen₂.hom.left ≫ ·) hgq.symm).trans (by rw [reassoc_of% c])
  obtain ⟨n, hn₁, hn₂⟩ : ∃ n : _ ⟶ pullback AW.A.hom (spMap j),
      n ≫ pullback.fst _ _ = ℓ ≫ gW ∧ n ≫ pullback.snd _ _ = s :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, wW', hℓ₂]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have : IsIso gi := inferInstanceAs (IsIso ((Over.forget _).map gen.inv))
  have hm : n ≫ p = π ≫ κ ≫ g₂ ≫ q := by
    refine hA₁.1.hom_ext ?_ ?_
    · rw [← cancel_mono gi, ← cancel_mono (pullback.fst G.hom (jK R))]
      simp only [Category.assoc]
      rw [reassoc_of% hp₁, reassoc_of% hn₁, hα', reassoc_of% hℓ₁, hgq', reassoc_of% hκ, hsq]
    · have k : π ≫ κ ≫ pullback.snd G₂.hom (jK R₂) = s ≫ spMap (l.comp i.symm.toRingHom) := by
        rw [← cancel_mono (jK R₂)]
        simp only [Category.assoc]
        rw [← pullback.condition, reassoc_of% hκ, hβW'.1.w, reassoc_of% hπ, e₂]
      simp only [Category.assoc]
      rw [hp₂, reassoc_of% hn₂, hq.1.w, reassoc_of% w₂', reassoc_of% k, e₃]
  have H₁ : LBIso (AW.L.pull (ℓ ≫ gW)) (UW.LG.L.pull (π ≫ pullback.fst GW'.hom (jK W₂) ≫ τ)) :=
    pull_both (a := gW) UW.ext ℓ rfl hℓ₁.symm
  have H₂ : LBIso (AW.L.pull (ℓ ≫ gW)) (A₁.L.pull (n ≫ p)) := pull_both hLp n hn₁.symm rfl
  have H₃ : LBIso (A₂.L.pull ((π ≫ κ) ≫ g₂)) (A₁.L.pull (n ≫ p)) :=
    pull_right hLq _ (by simp only [hm, Category.assoc])
  have hG := UW.LG.isLB
  have H : LBIso ((UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)).pull π) (((A₂.L.pull g₂).pull κ).pull π) :=
    pull_pull (pull_pull (pull_pull (LBIso.trans (pull_isLB A₂.isLB _) (pull_isLB A₁.isLB _) (pull_isLB hG _) H₃
      (LBIso.trans (pull_isLB A₁.isLB _) (pull_isLB AW.isLB _) (pull_isLB hG _) H₂.symm H₁)))).symm
  let g' : pullback GW'.hom (jK W₂) ⟶ AW'.A.left := UW'.gen.hom.left
  have : IsIso g' := inferInstanceAs (IsIso ((Over.forget _).map UW'.gen.hom))
  have w' : g' ≫ AW'.A.hom = pullback.snd GW'.hom (jK W₂) := Over.w UW'.gen.hom
  have := AW'.isAb.smooth
  have := AW'.isAb.proper
  have hc := AW'.isAb.geomConnected
  have hD := (lb_gen_iso_descend_field (FractionRing W₂) Ω' j₂ _ _ (pullback.snd GW'.hom (jK W₂)) s π
    (by rw [← w']; infer_instance) (by rw [← w']; infer_instance)
    (by rw [← w']; exact (MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id (g' ≫ AW'.A.hom)).symm⟩) hc))
    (IsPullback.of_hasPullback _ _)).2 _ _ (pull_isLB hG _) (pull_isLB (pull_isLB A₂.isLB _) _) H
  exact LBIso.trans (pull_isLB UW'.LG.isLB _) (pull_isLB hG _) (pull_isLB (pull_isLB A₂.isLB _) _) hL hD

end GlobalTheory
