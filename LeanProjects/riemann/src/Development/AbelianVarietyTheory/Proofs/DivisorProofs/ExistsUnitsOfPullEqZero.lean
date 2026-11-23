import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqOfMulEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.SmallGlue
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SmallGlue

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (q : Y ⟶ X)
    (h : GlobalTheory.CechPic.pull q (cls L hL) = 0) :
    ∃ a : ∀ j, Γ(Y, q ⁻¹ᵁ L.U j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : L.ι),
      q (f z) ∈ L.U i → q (f z) ∈ L.U j →
      gm f z (q ⁻¹ᵁ L.U i) (a i) = gm (f ≫ q) z (L.U i ⊓ L.U j) (L.g i j) * gm f z (q ⁻¹ᵁ L.U j) (a j) := by
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hL q)).1 h
  have le : ∀ j, q ⁻¹ᵁ L.U j ≤ (L.pull q).U (fun _ => j) := fun j y hy => mem_pull.2 hy
  refine ⟨fun j => res (le j) (t.s (fun _ => j)), fun Z f z i j hi hj => ?_⟩
  have hm : f z ∈ (L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  have := congrArg (gm f z _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res _ z _ hm, gm_res _ z _ hm] at this
  rw [gm_res f z (le i) hi, gm_res f z (le j) hj]
  exact this.trans (congrArg (· * _) (gm_pull_g L q f z (fun _ => i) (fun _ => j) hm.1 hm.2))

theorem pullU_isGen_of_germ {X Y : Scheme.{0}} {L : LB X} (q : Y ⟶ X) (d : ∀ j, Γ(X, L.U j)ˣ) (i j : L.ι)
    (h : ∀ y : Y, q y ∈ L.U i → q y ∈ L.U j →
      gm (𝟙 Y) y (q ⁻¹ᵁ L.U i) (pullU q _ (d i)) =
        gm (𝟙 Y ≫ q) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (q ⁻¹ᵁ L.U j) (pullU q _ (d j))) :
    pullU q (L.U i ⊓ L.U j) (res inf_le_left (d i)) =
      pullU q (L.U i ⊓ L.U j) (L.g i j * res inf_le_right (d j)) := by
  refine unit_ext fun y hy => ?_
  have hm : q ((𝟙 Y : Y ⟶ Y) y) ∈ L.U i ⊓ L.U j := hy
  have e := h y hm.1 hm.2
  rw [gm_pull (𝟙 Y) q y _ hm.1, gm_pull (𝟙 Y) q y _ hm.2] at e
  rw [gm_pull (𝟙 Y) q y _ hm, gm_pull (𝟙 Y) q y _ hm, map_mul, gm_res (𝟙 Y ≫ q) y _ hm,
    gm_res (𝟙 Y ≫ q) y _ hm]
  exact e

theorem cech_patching : ∀ {X X₁ X₂ X₀ : Scheme.{0}} (ι₁ : X₁ ⟶ X) (ι₂ : X₂ ⟶ X) (ρ₁ : X₀ ⟶ X₁) (ρ₂ : X₀ ⟶ X₂), ρ₁ ≫ ι₁ = ρ₂ ≫ ι₂ →
    (∀ u : Γ(X₀, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : X₀, gm ρ₁ x ⊤ v = gm (𝟙 X₀) x ⊤ u) →
    (∀ (U : X.Opens) (a₁ : Γ(X₁, ι₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(X₂, ι₂ ⁻¹ᵁ U)ˣ),
      (∀ x : X₀, ρ₁ x ∈ ι₁ ⁻¹ᵁ U → gm ρ₁ x (ι₁ ⁻¹ᵁ U) a₁ = gm ρ₂ x (ι₂ ⁻¹ᵁ U) a₂) →
      ∃ d : Γ(X, U)ˣ, pullU ι₁ U d = a₁ ∧ pullU ι₂ U d = a₂) →
    (∀ (U : X.Opens) (d d' : Γ(X, U)ˣ), pullU ι₁ U d = pullU ι₁ U d' → pullU ι₂ U d = pullU ι₂ U d' → d = d') →
    ∀ c : Pic X, GlobalTheory.CechPic.pull ι₁ c = 0 → GlobalTheory.CechPic.pull ι₂ c = 0 → c = 0 := by
  intro X X₁ X₂ X₀ ι₁ ι₂ ρ₁ ρ₂ hsq hlift hpatch huniq c h₁ h₂
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨α, hα⟩ := exists_units_of_pull_eq_zero hL ι₁ h₁
  obtain ⟨β, hβ⟩ := exists_units_of_pull_eq_zero hL ι₂ h₂
  have pt : ∀ x : X₀, ι₂ (ρ₂ x) = ι₁ (ρ₁ x) := fun x => congrArg (fun g => g x) hsq.symm
  have le : ∀ j, ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ρ₂ ⁻¹ᵁ (ι₂ ⁻¹ᵁ L.U j) := fun j x hx => by
    show ι₂ (ρ₂ x) ∈ L.U j
    rw [pt]; exact hx
  have hu : ∀ j (x : X₀), ι₁ (ρ₁ x) ∈ L.U j →
      gm (𝟙 X₀) x (ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹) =
        gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ := fun j x hx => by
    rw [map_mul, map_inv, gm_res (𝟙 X₀) x (le j) hx, gm_pull (𝟙 X₀) ρ₁ x _ hx,
      gm_pull (𝟙 X₀) ρ₂ x _ (le j hx), Category.id_comp, Category.id_comp]
  obtain ⟨w, hw⟩ := glue_unit (⊤ : X₀.Opens) (fun j => ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (ι₁ (ρ₁ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩)
    (fun j => pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹)
    (fun i j x hx => by
      refine (hu i x hx.1).trans (Eq.trans ?_ (hu j x hx.2).symm)
      rw [hα _ ρ₁ x i j hx.1 hx.2, hβ _ ρ₂ x i j (le i hx.1) (le j hx.2), hsq, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨v, hv⟩ := hlift w
  have hd : ∀ j, ∃ d : Γ(X, L.U j)ˣ, pullU ι₁ _ d = α j * (res le_top v)⁻¹ ∧ pullU ι₂ _ d = β j := fun j =>
    hpatch _ _ _ fun x hx => by
      have e : gm (𝟙 X₀) x ⊤ w = gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ :=
        (gm_res (𝟙 X₀) x (le_top : ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ⊤) hx w).symm.trans
          ((congrArg _ (hw j)).trans (hu j x hx))
      rw [map_mul, map_inv, gm_res ρ₁ x _ hx, hv, e, mul_inv, inv_inv, mul_inv_cancel_left]
  choose d hd₁ hd₂ using hd
  refine (cls_eq_zero_iff hL).2 ⟨⟨d⟩, fun i j => huniq _ _ _ ?_ ?_⟩
  · refine pullU_isGen_of_germ ι₁ d i j fun y hi hj => ?_
    rw [hd₁, hd₁, map_mul, map_mul, map_inv, map_inv, gm_res (𝟙 X₁) y _ hi, gm_res (𝟙 X₁) y _ hj,
      hα _ (𝟙 X₁) y i j hi hj, _root_.mul_assoc]
  · refine pullU_isGen_of_germ ι₂ d i j fun y hi hj => ?_
    rw [hd₂, hd₂]
    exact hβ _ (𝟙 X₂) y i j hi hj

end GlobalTheory.SmallGlue
