import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem degGen_holds : DegGen := by
  intro E _ Γ _ X O _ _ K₀ K₁ i Y Y' pY π' s h01 hQ0 hQ1 Ω _ _ y σ hy
  let T : ∀ u : Γ, u ∈ K₀ → (X.Z i ⟶ X.Z i) := fun u hu => X.tr i i u (hQ0.adm u hu).1 (hQ0.adm u hu).2
  have hT : ∀ a b (ha : a ∈ K₀) (hb : b ∈ K₀), T a ha ≫ T b hb = T (b * a) (K₀.mul_mem hb ha) :=
    fun a b ha hb => X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  have hTc : ∀ a b (ha : a ∈ K₀) (hb : b ∈ K₀), a = b → T a ha = T b hb := by
    rintro a b ha hb rfl
    rfl
  have h1 : ∀ h1 : (1 : Γ) ∈ K₀, T 1 h1 = 𝟙 _ := fun h1 => X.tr_self _ _ _ _ (X.K i).one_mem
  have hinv1 : ∀ w (hw : w ∈ K₀), w ∈ K₁ → T w hw ≫ π' = π' := fun w hw hw1 =>
    hQ1.inv w hw1 _ _
  have hinv0 : ∀ w (hw : w ∈ K₀), T w hw ≫ π' ≫ s = π' ≫ s := fun w hw => hQ0.inv w hw _ _
  obtain ⟨x, hx⟩ := hQ0.onto Ω y σ hy
  let f : K₀ → { y' // y' ≫ s = y } := fun u =>
    ⟨x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ π', by
      rw [Category.assoc, Category.assoc, hinv0 _ (K₀.inv_mem u.2), hx]⟩
  have key : ∀ u v : K₀, f u = f v ↔ (u : Γ)⁻¹ * v ∈ K₁ := by
    intro u v
    constructor
    · intro h
      have hv : (x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2)) ≫ π' = (x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2)) ≫ π' := by
        simpa [f] using congrArg Subtype.val h
      obtain ⟨w, hw1, a, b, he⟩ := hQ1.fib Ω _ _ hv
      have hw0 := h01 hw1
      have he' : x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2) = x ≫ T (w * (u : Γ)⁻¹) (K₀.mul_mem hw0 (K₀.inv_mem u.2)) := by
        rw [he, Category.assoc]
        exact congrArg (x ≫ ·) (hT _ _ (K₀.inv_mem u.2) hw0)
      have hm : v.1 * w * (u : Γ)⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem v.2 hw0) (K₀.inv_mem u.2)
      have hfix : x ≫ T (v.1 * w * (u : Γ)⁻¹) hm = x := by
        have p1 : w * (u : Γ)⁻¹ ∈ K₀ := K₀.mul_mem hw0 (K₀.inv_mem u.2)
        have e1 : T (v.1 * w * (u : Γ)⁻¹) hm = T (w * (u : Γ)⁻¹) p1 ≫ T v.1 v.2 :=
          (hTc _ _ hm (K₀.mul_mem v.2 p1) (by group)).trans (hT _ _ p1 v.2).symm
        have e2 : T (v : Γ)⁻¹ (K₀.inv_mem v.2) ≫ T v.1 v.2 = 𝟙 _ :=
          (hT _ _ (K₀.inv_mem v.2) v.2).trans
            ((hTc _ _ (K₀.mul_mem v.2 (K₀.inv_mem v.2)) K₀.one_mem (by group)).trans (h1 K₀.one_mem))
        rw [e1, ← Category.assoc, ← he', Category.assoc, e2, Category.comp_id]
      have ht := hQ0.free _ hm _ _ Ω x hfix
      have hc := (hQ0.adm _ (K₀.inv_mem u.2)).2 _ ht
      have := K₁.mul_mem (hQ1.le hc) (K₁.inv_mem hw1)
      convert this using 1
      group
    · intro h
      apply Subtype.ext
      show x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ π' = x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2) ≫ π'
      have hk : ((u : Γ)⁻¹ * v)⁻¹ ∈ K₀ := h01 (K₁.inv_mem h)
      have e : T (v : Γ)⁻¹ (K₀.inv_mem v.2) = T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ T _ hk :=
        (hTc _ _ (K₀.inv_mem v.2) (K₀.mul_mem hk (K₀.inv_mem u.2)) (by group)).trans
          (hT _ _ (K₀.inv_mem u.2) hk).symm
      rw [e, Category.assoc, hinv1 _ hk (K₁.inv_mem h)]
  let F : K₀ ⧸ K₁.subgroupOf K₀ → { y' // y' ≫ s = y } := Quotient.lift f (fun u v huv =>
    (key u v).2 (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp huv)))
  have hinj : Function.Injective F := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H u =>
      induction b using QuotientGroup.induction_on with
      | H v =>
        intro h
        exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ((key u v).1 h))
  have hsurj : Function.Surjective F := by
    rintro ⟨y', hy'⟩
    obtain ⟨x', hx'⟩ := hQ1.onto Ω y' σ (by rw [← Category.assoc, hy', hy])
    obtain ⟨u, hu, a, b, hxe⟩ := hQ0.fib Ω x x' (by rw [hx, ← Category.assoc, hx', hy'])
    refine ⟨QuotientGroup.mk ⟨u⁻¹, K₀.inv_mem hu⟩, ?_⟩
    apply Subtype.ext
    show x ≫ T (u⁻¹)⁻¹ (K₀.inv_mem (K₀.inv_mem hu)) ≫ π' = y'
    rw [hTc (u⁻¹)⁻¹ u (K₀.inv_mem (K₀.inv_mem hu)) hu (inv_inv u), ← Category.assoc]
    rw [← hx', hxe]
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).symm

end UpperTheory.Gal.FiniteEtaleModels
