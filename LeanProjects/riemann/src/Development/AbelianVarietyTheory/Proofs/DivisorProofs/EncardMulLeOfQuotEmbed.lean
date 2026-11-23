import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_of_quot_embed : ∀ (G : Type) [AddCommGroup G] (Λ Λ' Λ₀ Λ₀' : AddSubgroup G) (B E : ℝ → Set G)
    (T : G →+ G), IsBallFam Λ B → IsBallFam Λ' E → (∀ u ∈ B 1, T u ∈ E 1) → (∀ u ∈ Λ, T u ∈ Λ₀' → u ∈ Λ₀) →
    (B 1).Finite → (B 1).encard * (E 1 ∩ Λ₀').encard ≤ (B 2 ∩ Λ₀).encard * (E 2).encard := by
  intro G _ Λ Λ' Λ₀ Λ₀' B E T hB hE hT hpull _
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  let q : G → G ⧸ Λ₀ := QuotientAddGroup.mk
  let R : Set (G ⧸ Λ₀) := q '' B 1
  let s : G ⧸ Λ₀ → G := Function.invFunOn q (B 1)
  have hs_mem : ∀ c ∈ R, s c ∈ B 1 := fun c hc => Function.invFunOn_mem hc
  have hs_eq : ∀ c ∈ R, q (s c) = c := fun c hc => Function.invFunOn_eq hc

  have h1 : (B 1).encard ≤ R.encard * (B 2 ∩ Λ₀ : Set G).encard := by
    rw [← Set.encard_prod]
    refine le_trans (Set.encard_le_encard (s := B 1)
      (t := (fun p : (G ⧸ Λ₀) × G => s p.1 + p.2) '' (R ×ˢ (B 2 ∩ (Λ₀ : Set G)))) ?_) (Set.encard_image_le _ _)
    intro x hx
    have hqx : q x ∈ R := ⟨x, hx, rfl⟩
    refine ⟨(q x, x - s (q x)), ⟨hqx, ?_, ?_⟩, by simp⟩
    · have := hB.sub_mem 1 1 x (s (q x)) hx (hs_mem _ hqx)
      rwa [h2] at this
    · have he : q (s (q x)) = q x := hs_eq _ hqx
      have := (QuotientAddGroup.eq).mp he
      show x - s (q x) ∈ Λ₀
      rwa [sub_eq_neg_add]

  have h3 : R.encard * (E 1 ∩ Λ₀' : Set G).encard ≤ (E 2).encard := by
    rw [← Set.encard_prod]
    refine Set.encard_le_encard_of_injOn (f := fun p : (G ⧸ Λ₀) × G => T (s p.1) - p.2) ?_ ?_
    · rintro ⟨c, v⟩ ⟨hc, hv, -⟩
      have := hE.sub_mem 1 1 _ _ (hT _ (hs_mem c hc)) hv
      rwa [h2] at this
    · rintro ⟨c, v⟩ ⟨hc, hv, hv'⟩ ⟨c', w⟩ ⟨hc', hw, hw'⟩ heq
      simp only at heq
      have hd : T (s c - s c') ∈ Λ₀' := by
        have : T (s c - s c') = v - w := by rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp heq
        rw [this]; exact Λ₀'.sub_mem hv' hw'
      have hΛ : s c - s c' ∈ Λ := Λ.sub_mem (hB.subset 1 (hs_mem c hc)) (hB.subset 1 (hs_mem c' hc'))
      have h0 : s c - s c' ∈ Λ₀ := hpull _ hΛ hd
      have hqq : q (s c) = q (s c') := by
        apply (QuotientAddGroup.eq).mpr
        have := Λ₀.neg_mem h0
        rwa [neg_sub, sub_eq_neg_add] at this
      have hcc : c = c' := by rw [← hs_eq c hc, ← hs_eq c' hc', hqq]
      subst hcc
      have : v = w := by simpa using heq
      rw [this]
  calc (B 1).encard * (E 1 ∩ Λ₀' : Set G).encard
      ≤ (R.encard * (B 2 ∩ Λ₀ : Set G).encard) * (E 1 ∩ Λ₀' : Set G).encard := by gcongr
    _ = (B 2 ∩ Λ₀ : Set G).encard * (R.encard * (E 1 ∩ Λ₀' : Set G).encard) := by ring
    _ ≤ (B 2 ∩ Λ₀ : Set G).encard * (E 2).encard := by gcongr

end GlobalTheory.VolBr
