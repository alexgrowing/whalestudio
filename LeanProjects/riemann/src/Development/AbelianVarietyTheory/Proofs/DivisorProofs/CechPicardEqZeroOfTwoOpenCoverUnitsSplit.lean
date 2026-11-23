import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPic

open TopologicalSpace

theorem exists_units_of_gen_restrict {Z : Scheme.{0}} (L : LB Z) (O : Z.Opens) (t : LB.Gen (L.pull O.ι))
    (ht : t.IsGen) : ∃ b : ∀ i, Γ(Z, L.U i ⊓ O)ˣ, ∀ (i j : L.ι) (x : Z), x ∈ L.U i → x ∈ L.U j → x ∈ O →
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) = gm (𝟙 Z) x (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Z) x (L.U j ⊓ O) (b j) := by
  choose c hc using fun i : L.ι => exists_ext_unit O.ι ((L.pull O.ι).U (fun _ => i)) (t.s (fun _ => i))
  have le : ∀ i, L.U i ⊓ O ≤ O.ι ''ᵁ ((L.pull O.ι).U (fun _ => i)) := by
    intro i x hx
    have m : (⟨x, hx.2⟩ : O.toScheme) ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hx.1
    exact ⟨⟨x, hx.2⟩, m, rfl⟩
  refine ⟨fun i => res (le i) (c i), fun i j x hi hj hx => ?_⟩
  let z : O.toScheme := ⟨x, hx⟩
  have mi : z ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hi
  have mj : z ∈ (L.pull O.ι).U (fun _ => j) := mem_pull.2 hj
  have hW : O.ι z ∈ L.U i ⊓ L.U j ⊓ O := ⟨⟨hi, hj⟩, hx⟩
  have hWi : O.ι z ∈ L.U i ⊓ O := ⟨hi, hx⟩
  have hWj : O.ι z ∈ L.U j ⊓ O := ⟨hj, hx⟩
  have hWij : O.ι z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have l₁ : L.U i ⊓ L.U j ⊓ O ≤ L.U i ⊓ L.U j := inf_le_left
  have l₂ : L.U i ⊓ L.U j ⊓ O ≤ L.U j ⊓ O := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have key := gm_inj O.ι z (U := L.U i ⊓ O) (U' := L.U i ⊓ L.U j ⊓ O) hWi hW
    (a := res (le i) (c i)) (b := res l₁ (L.g i j) * res l₂ (res (le j) (c j))) (by
      rw [map_mul, gm_res O.ι z l₁ hW, gm_res O.ι z l₂ hW, gm_res O.ι z (le j) hWj, gm_res O.ι z (le i) hWi]
      have e₁ := hc i O.toScheme (𝟙 _) z mi
      have e₂ := hc j O.toScheme (𝟙 _) z mj
      rw [Category.id_comp] at e₁ e₂
      rw [e₁, e₂, (isGen_iff_germ t).1 ht z _ _ mi mj, gm_pull_g L O.ι (𝟙 _) z _ _ mi mj, Category.id_comp])
  rw [map_mul, gm_res (𝟙 Z) (O.ι z) l₁ hW, gm_res (𝟙 Z) (O.ι z) l₂ hW] at key
  exact key

theorem eq_zero_of_pull_eq_zero_of_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ →
    (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ),
      F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') →
    ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  intro Z O O' hcov hsplit c hc hc'
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  rw [← cls_pull hL O.ι (pull_isLB hL O.ι)] at hc
  rw [← cls_pull hL O'.ι (pull_isLB hL O'.ι)] at hc'
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hc
  obtain ⟨t', ht'⟩ := (cls_eq_zero_iff _).1 hc'
  obtain ⟨b, hb⟩ := exists_units_of_gen_restrict L O t ht
  obtain ⟨b', hb'⟩ := exists_units_of_gen_restrict L O' t' ht'
  have key₁ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y => by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have key₂ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * y * x⁻¹ = a * y := fun a x y => by
    rw [mul_right_comm, mul_inv_cancel_right]

  let W : L.ι → Z.Opens := fun i => L.U i ⊓ (O ⊓ O')
  have lw : ∀ i, W i ≤ L.U i ⊓ O := fun i => inf_le_inf_left _ inf_le_left
  have lw' : ∀ i, W i ≤ L.U i ⊓ O' := fun i => inf_le_inf_left _ inf_le_right
  let q : ∀ i, Γ(Z, W i)ˣ := fun i => res (lw i) (b i) * (res (lw' i) (b' i))⁻¹
  have gq : ∀ i x, x ∈ W i → gm (𝟙 Z) x (W i) (q i) =
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) * (gm (𝟙 Z) x (L.U i ⊓ O') (b' i))⁻¹ := fun i x hx => by
    simp only [q, map_mul, map_inv, gm_res (𝟙 Z) x (lw i) hx, gm_res (𝟙 Z) x (lw' i) hx]
  obtain ⟨F, hF⟩ := glue_unit (O ⊓ O') W (fun i => inf_le_right) (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hi, hx⟩) q (fun i j x hx => by
      rw [gq i x hx.1, gq j x hx.2, hb i j x hx.1.1 hx.2.1 hx.1.2.1, hb' i j x hx.1.1 hx.2.1 hx.1.2.2, key₁])
  obtain ⟨u, u', hu⟩ := hsplit F

  have gF : ∀ i x, x ∈ W i → gm (𝟙 Z) x (L.U i ⊓ O) (b i) =
      gm (𝟙 Z) x (L.U i ⊓ O') (b' i) * gm (𝟙 Z) x O u * gm (𝟙 Z) x O' u' := fun i x hx => by
    have e := congrArg (gm (𝟙 Z) x (W i)) (hF i)
    rw [gm_res (𝟙 Z) x _ hx, gq i x hx, hu, map_mul, gm_res (𝟙 Z) x _ hx.2, gm_res (𝟙 Z) x _ hx.2] at e
    rw [(mul_inv_eq_iff_eq_mul).1 e.symm]
    ac_rfl

  have loc : ∀ i, ∃ s : Γ(Z, L.U i)ˣ,
      (∀ y, y ∈ L.U i → y ∈ O → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹) ∧
      (∀ y, y ∈ L.U i → y ∈ O' → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u') := by
    intro i
    let V : Bool → Z.Opens := fun β => Bool.rec (L.U i ⊓ O') (L.U i ⊓ O) β
    let v : ∀ β, Γ(Z, V β)ˣ := fun β => Bool.rec (motive := fun β => Γ(Z, V β)ˣ)
      (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) β
    have hV : ∀ β, V β ≤ L.U i := fun β => by cases β <;> exact inf_le_left
    have g₁ : ∀ y, y ∈ L.U i ⊓ O → gm (𝟙 Z) y (V true) (v true) =
        gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹ := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O) (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) = _
      rw [map_mul, map_inv, gm_res (𝟙 Z) y _ hy]
    have g₀ : ∀ y, y ∈ L.U i ⊓ O' → gm (𝟙 Z) y (V false) (v false) =
        gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u' := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O') (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') = _
      rw [map_mul, gm_res (𝟙 Z) y _ hy]
    obtain ⟨s, hs⟩ := glue_unit (L.U i) V hV (fun y hy => by
        have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
        rcases Opens.mem_sup.1 h with h | h
        · exact Opens.mem_iSup.2 ⟨true, hy, h⟩
        · exact Opens.mem_iSup.2 ⟨false, hy, h⟩) v (fun β β₂ y hy => by
        cases β <;> cases β₂
        · rfl
        · rw [g₀ y hy.1, g₁ y hy.2, gF i y ⟨hy.1.1, hy.2.2, hy.1.2⟩, key₂]
        · rw [g₁ y hy.1, g₀ y hy.2, gF i y ⟨hy.1.1, hy.1.2, hy.2.2⟩, key₂]
        · rfl)
    refine ⟨s, fun y hi ho => ?_, fun y hi ho => ?_⟩
    · have e := congrArg (gm (𝟙 Z) y (V true)) (hs true)
      rw [gm_res (𝟙 Z) y (hV true) (show y ∈ L.U i ⊓ O from ⟨hi, ho⟩)] at e
      exact e.trans (g₁ y ⟨hi, ho⟩)
    · have e := congrArg (gm (𝟙 Z) y (V false)) (hs false)
      rw [gm_res (𝟙 Z) y (hV false) (show y ∈ L.U i ⊓ O' from ⟨hi, ho⟩)] at e
      exact e.trans (g₀ y ⟨hi, ho⟩)
  choose s hs using loc
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, (isGen_iff_germ _).2 fun y i j hi hj => ?_⟩
  have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
  rcases Opens.mem_sup.1 h with h | h
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).1 y hi h, (hs j).1 y hj h, hb i j y hi hj h, _root_.mul_assoc]
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).2 y hi h, (hs j).2 y hj h, hb' i j y hi hj h, _root_.mul_assoc]

end GlobalTheory.CechPic
