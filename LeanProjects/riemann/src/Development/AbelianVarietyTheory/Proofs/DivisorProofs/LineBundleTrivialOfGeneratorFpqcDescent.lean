import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.FlatDescent

theorem injective_app_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : Function.Injective (p.app U) := by
  have := effectiveEpi_morphismRestrict p U
  intro a b hab
  have hb : Function.Bijective U.topIso.inv := ConcreteCategory.bijective_of_isIso _
  apply hb.1
  apply injective_appTop_of_epi (p ∣_ U)
  rw [appTop_morphismRestrict_apply, appTop_morphismRestrict_apply, hab]

theorem unit_ext_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {U : X.Opens} {a b : Γ(X, U)ˣ} (h : ∀ y : Y, p y ∈ U → gm p y U a = gm p y U b) : a = b := by
  have e : pullU p U a = pullU p U b := unit_ext fun y hy => by
    rw [gm_pull (𝟙 Y) p y U hy, gm_pull (𝟙 Y) p y U hy, Category.id_comp]
    exact h y hy
  exact Units.ext (injective_app_of_flat p U (congrArg Units.val e))

theorem exists_unit_of_gm_eq {X X' Z : Scheme.{0}} (f : X' ⟶ X) [Flat f] [Surjective f] [QuasiCompact f]
    {g₁ g₂ : Z ⟶ X'} (h : IsPullback g₁ g₂ f f) (U : X.Opens) (s : Γ(X', f ⁻¹ᵁ U)ˣ)
    (hs : ∀ z : Z, f (g₁ z) ∈ U → gm g₁ z _ s = gm g₂ z _ s) :
    ∃ a : Γ(X, U)ˣ, pullU f U a = s := by
  have hg : g₁ ⁻¹ᵁ f ⁻¹ᵁ U ≤ g₂ ⁻¹ᵁ f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h.w]
  have e : res le_rfl (pullU g₁ _ s) = res hg (pullU g₂ _ s) := unit_ext fun z hz => by
    rw [gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 Z) g₁ z _ hz, gm_pull (𝟙 Z) g₂ z _ (hg hz),
      Category.id_comp, Category.id_comp]
    exact hs z hz
  obtain ⟨a, ha, -⟩ := (existsUnique_app_eq_iff f h U _ rfl le_rfl hg s.val).2 (congrArg Units.val e)
  obtain ⟨a, rfl⟩ := (isUnit_app_iff f U a).1 (ha ▸ s.isUnit)
  exact ⟨a, Units.ext ha⟩

theorem triv_of_gen_descent : ∀ {X X' Z : Scheme.{0}} (M : LB X), M.IsLB → ∀ (f : X' ⟶ X), Flat f →
    Surjective f → QuasiCompact f → ∀ (g₁ g₂ : Z ⟶ X'), IsPullback g₁ g₂ f f →
    ∀ t : LB.Gen (M.pull f), t.IsGen →
    (∀ (z : Z) (J : (Z ⟶ X) → M.ι), Geo.Tor.Good M z J → val t g₁ z J = val t g₂ z J) → Triv M := by
  intro X X' Z M hM f _ _ _ g₁ g₂ h t ht hv
  have le : ∀ i, f ⁻¹ᵁ M.U i ≤ LB.wchart M (fun _ : PUnit => f) (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  have ex : ∀ i, ∃ a : Γ(X, M.U i)ˣ, pullU f _ a = res (le i) (t.s fun _ => i) := fun i =>
    exists_unit_of_gm_eq f h (M.U i) _ fun z hz => by
      have hz₂ : f (g₂ z) ∈ M.U i := (congrArg (fun q : Z ⟶ X => q z ∈ M.U i) h.w).mp hz
      obtain ⟨J, hJ, eJ⟩ := exists_good M hM z (fun _ : PUnit => g₁ ≫ f) (fun _ => i)
        (fun _ _ _ => rfl) (fun _ => hz)
      have v := hv z J hJ
      rw [val_of t g₁ z J (fun _ => i) eJ,
        val_of t g₂ z J (fun _ => i) (fun k => h.w ▸ eJ k)] at v
      exact (gm_res g₁ z _ hz _).trans (v.trans (gm_res g₂ z _ hz₂ _).symm)
  choose a ha using ex
  have ga : ∀ i (y : X'), f y ∈ M.U i →
      gm f y (M.U i) (a i) = gm (𝟙 X') y (LB.wchart M (fun _ : PUnit => f) (fun _ => i)) (t.s fun _ => i) :=
    fun i y hy => by
      have := gm_pull (𝟙 X') f y (M.U i) hy (a i)
      rw [Category.id_comp, ha] at this
      exact this.symm.trans (gm_res (𝟙 X') y (le i) hy _)
  refine ⟨⟨a⟩, fun i j => unit_ext_of_flat f fun y hy => ?_⟩
  have c := gen_trans ht (𝟙 X') y (j := fun _ => i) (j' := fun _ => j) (le i hy.1) (le j hy.2)
  rw [← ga i y hy.1, ← ga j y hy.2, trF, Fintype.prod_unique, zpow_one, Category.id_comp] at c
  exact (gm_res f y _ hy _).trans (c.trans ((map_mul _ _ _).trans (congrArg _ (gm_res f y _ hy _))).symm)

end GlobalTheory.FlatDescent
