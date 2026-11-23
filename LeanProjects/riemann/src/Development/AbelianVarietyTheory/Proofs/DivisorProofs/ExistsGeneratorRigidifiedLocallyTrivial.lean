import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.RigTriv

variable {T X : Scheme.{0}}

theorem exists_lift (W : X.Opens) {Z : Scheme.{0}} (f : Z ⟶ X) (h : ∀ z, f z ∈ W) :
    ∃ g : Z ⟶ W.toScheme, g ≫ W.ι = f :=
  ⟨IsOpenImmersion.lift W.ι f (by rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact h z),
    IsOpenImmersion.lift_fac _ _ _⟩

theorem ι_mem (W : X.Opens) (x : W.toScheme) : W.ι x ∈ W := by
  have h : W.ι x ∈ Set.range W.ι := ⟨x, rfl⟩
  rw [W.range_ι] at h; exact h

theorem surj_restrict (A : Over T) [GrpObj A] (hA : IsAbelianScheme A) (U : T.Opens) :
    Function.Surjective (A.hom ∣_ U).appTop.hom := by
  have h1 : Function.Surjective (pullback.snd A.hom U.ι).appTop.hom :=
    (GlobalTheory.SemiRigid.globalFns _ _ (Out.TLinPf.isAb_pullback U.ι A hA)).2
  have e : A.hom ∣_ U = (pullbackRestrictIsoRestrict A.hom U).inv ≫ pullback.snd A.hom U.ι := rfl
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso
    ((pullbackRestrictIsoRestrict A.hom U).inv.app ⊤)).2.comp h1

theorem normalize (p : X ⟶ T) (e : T ⟶ X) {N : LB X} (hN : N.IsLB)
    (t : LB.Gen (N.pull e)) (ht : t.IsGen) (W : X.Opens) (hW : ∀ x ∈ W, e (p x) ∈ W)
    (s : LB.Gen (N.pull W.ι)) (hs : s.IsGen) :
    ∃ n : LB.Gen (LB.LinComb N (fun _ : PUnit => W.ι ≫ 𝟙 X) (fun _ => 1)), n.IsGen ∧
      ∀ (Z : Scheme.{0}) (m : Z ⟶ W.toScheme) (z : Z) (J), Good N z J →
        m ≫ W.ι ≫ p ≫ e = m ≫ W.ι → val n m z J = val t (m ≫ W.ι ≫ p) z J := by
  obtain ⟨q, hq⟩ := exists_lift W (W.ι ≫ p ≫ e) (fun z => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hW _ (ι_mem W z))
  let n₀ := LB.mulGen N _ _ _ _ (LB.mulGen N _ _ _ _ s (LB.invGen N _ _ (LB.pullGen N _ _ s q)))
    (LB.pullGen N (fun _ : PUnit => e) (fun _ => 1) t (W.ι ≫ p))
  have hn₀ : n₀.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hs
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hs _))) (DVR.pullGen_isGen _ _ _ _ ht _)
  obtain ⟨n, hn, hv⟩ := exists_gen hN (φ' := fun _ : PUnit => W.ι ≫ 𝟙 X) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, zpow_one,
        zpow_neg, hq, Category.assoc, Category.comp_id]
      exact _root_.inv_mul_cancel_right _ _) n₀ hn₀
  refine ⟨n, hn, fun Z m z J hJ hm => ?_⟩
  have hmq : m ≫ q = m := by
    rw [← cancel_mono W.ι, Category.assoc, hq, hm]
  rw [hv Z m z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, hmq, mul_inv_cancel, _root_.one_mul]

theorem exists_gen_of_local (p : X ⟶ T) (e : T ⟶ X) (he : e ≫ p = 𝟙 T)
    (hsurj : ∀ U : T.Opens, Function.Surjective (p ∣_ U).appTop.hom) {N : LB X} (hN : N.IsLB)
    (t : LB.Gen (N.pull e)) (ht : t.IsGen)
    (hloc : ∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : LB.Gen (N.pull (p ⁻¹ᵁ V).ι), s.IsGen) :
    ∃ s : LB.Gen N, s.IsGen := by
  choose V hV s hs using hloc
  have hep : ∀ x : T, p (e x) = x := fun x => by rw [← Scheme.Hom.comp_apply, he]; rfl
  have hW : ∀ τ, ∀ x ∈ p ⁻¹ᵁ V τ, e (p x) ∈ p ⁻¹ᵁ V τ := fun τ x hx => by
    show p (e (p x)) ∈ V τ
    rw [hep]; exact hx
  choose n hn hnv using fun τ => normalize p e hN t ht (p ⁻¹ᵁ V τ) (hW τ) (s τ) (hs τ)
  have agree : ∀ (τ τ' : T) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ V τ).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ V τ').toScheme) (z : Z) (J), Good N z J →
      r ≫ (p ⁻¹ᵁ V τ).ι = r' ≫ (p ⁻¹ᵁ V τ').ι → val (n τ) r z J = val (n τ') r' z J := by
    intro τ τ' Z r r' z J hJ hrr
    set U := V τ ⊓ V τ' with hUdef
    have l₁ : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V τ := fun x hx => hx.1
    have l₂ : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V τ' := fun x hx => hx.2
    let i₁ := X.homOfLE l₁
    let i₂ := X.homOfLE l₂
    have hi₁ : i₁ ≫ (p ⁻¹ᵁ V τ).ι = (p ⁻¹ᵁ U).ι := X.homOfLE_ι _
    have hi₂ : i₂ ≫ (p ⁻¹ᵁ V τ').ι = (p ⁻¹ᵁ U).ι := X.homOfLE_ι _
    obtain ⟨e₂, he₂⟩ := exists_lift (p ⁻¹ᵁ U) (U.ι ≫ e) (fun y => by
      show p ((U.ι ≫ e) y) ∈ U
      rw [Scheme.Hom.comp_apply, hep]; exact ι_mem U y)
    have hs₂ : e₂ ≫ (p ∣_ U) = 𝟙 _ := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he₂, Category.assoc, he,
        Category.comp_id, Category.id_comp]
    obtain ⟨ρ, hρ⟩ := exists_lift (p ⁻¹ᵁ U) (r ≫ (p ⁻¹ᵁ V τ).ι) (fun y => by
      refine ⟨ι_mem (p ⁻¹ᵁ V τ) (r y), ?_⟩
      have h := ι_mem (p ⁻¹ᵁ V τ') (r' y)
      rw [← Scheme.Hom.comp_apply, ← hrr, Scheme.Hom.comp_apply] at h
      exact h)
    have hρ₁ : ρ ≫ i₁ = r := by rw [← cancel_mono (p ⁻¹ᵁ V τ).ι, Category.assoc, hi₁, hρ]
    have hρ₂ : ρ ≫ i₂ = r' := by rw [← cancel_mono (p ⁻¹ᵁ V τ').ι, Category.assoc, hi₂, hρ, hrr]
    have hφ : i₂ ≫ (p ⁻¹ᵁ V τ').ι ≫ 𝟙 X = i₁ ≫ (p ⁻¹ᵁ V τ).ι ≫ 𝟙 X := by
      rw [← Category.assoc, hi₂, ← Category.assoc, hi₁]
    obtain ⟨b', hb', hbv⟩ := exists_gen hN (φ' := fun _ : PUnit => i₁ ≫ (p ⁻¹ᵁ V τ).ι ≫ 𝟙 X)
      (ε' := fun _ => 1) (fun U _ h => by simp only [hφ]) (LB.pullGen N _ _ (n τ') i₂)
      (DVR.pullGen_isGen _ _ _ _ (hn τ') _)
    have sec : ∀ (σ : T) (l : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V σ), X.homOfLE l ≫ (p ⁻¹ᵁ V σ).ι = (p ⁻¹ᵁ U).ι →
        (e₂ ≫ X.homOfLE l) ≫ (p ⁻¹ᵁ V σ).ι ≫ p ≫ e = (e₂ ≫ X.homOfLE l) ≫ (p ⁻¹ᵁ V σ).ι := by
      intro σ l hl
      simp only [Category.assoc, reassoc_of% hl, reassoc_of% he₂, reassoc_of% he, hl, he₂]
    have key := gen_unique hN (p ∣_ U) e₂ hs₂ (hsurj U) (u := LB.pullGen N _ _ (n τ) i₁) (u' := b')
      (DVR.pullGen_isGen _ _ _ _ (hn τ) _) hb' (fun y J hJ => by
        rw [hbv _ _ y J hJ, val_pull hJ, val_pull hJ, hnv τ _ (e₂ ≫ i₁) y J hJ (sec τ l₁ hi₁),
          hnv τ' _ (e₂ ≫ i₂) y J hJ (sec τ' l₂ hi₂)]
        simp only [Category.assoc, reassoc_of% hi₁, reassoc_of% hi₂]) Z ρ z J hJ
    rw [val_pull hJ, hρ₁, hbv _ _ z J hJ, val_pull hJ, hρ₂] at key
    exact key
  obtain ⟨u, hu, -⟩ := glue_gen hN (fun _ : PUnit => 𝟙 X) (fun _ => 1) (fun τ => p ⁻¹ᵁ V τ)
    (fun x => ⟨p x, hV (p x)⟩) n hn agree
  have hle : ∀ i, N.U i ≤ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  refine ⟨⟨fun i => res (hle i) (u.s (fun _ => i))⟩, fun i j => unit_ext fun x hx => ?_⟩
  have h1 : (𝟙 X : X ⟶ X) x ∈ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => i) := hle i hx.1
  have h2 : (𝟙 X : X ⟶ X) x ∈ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => j) := hle j hx.2
  have key := gen_trans hu (𝟙 X) x h1 h2
  simp only [trF, Fintype.prod_unique, zpow_one, Category.comp_id] at key
  dsimp only
  rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx]
  exact (gm_res (𝟙 X) x (hle i) hx.1 _).trans (key.trans (congrArg _ (gm_res (𝟙 X) x (hle j) hx.2 _).symm))

theorem exists_gen_of_locally_trivial : ∀ (T : Scheme.{0}) (A' : Over T) [GrpObj A'] (N : LB A'.left), IsAbelianScheme A' → N.IsLB → Out.Rigidified A' N → (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : (N.pull (A'.hom ⁻¹ᵁ V).ι).Gen, s.IsGen) → ∃ s : N.Gen, s.IsGen := by
  intro T A' _ N hA hN ⟨t, ht⟩ hloc
  exact exists_gen_of_local A'.hom (eSec A') (Over.w η[A']) (surj_restrict A' hA) hN t ht hloc

end GlobalTheory.RigTriv
