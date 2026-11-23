import Mathlib

universe u_1 u_2

namespace GlobalTheory.PermutationExistence

theorem exists_perm {G : Type u_1} {C : Type u_2} [Group G] [AddCommMonoid C]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (h : G) (hh : h ∈ H) :
    ∃ σ : G → G, (∀ s ∈ S, σ s ∈ S ∧ (σ s)⁻¹ * (h * s) ∈ V) ∧
      ∀ f : G → C, ∑ s ∈ S, f (σ s) = ∑ s ∈ S, f s := by
  classical
  have key : ∀ s ∈ S, ∃ s' : G, s' ∈ S ∧ s'⁻¹ * (h * s) ∈ V := fun s hs =>
    (hT (h * s) (H.mul_mem hh (hS s hs))).exists
  choose! σ hσS hσV using key
  refine ⟨σ, fun s hs => ⟨hσS s hs, hσV s hs⟩, fun f => ?_⟩

  have hinj : Set.InjOn σ S := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := hσV s₁ hs₁
    rw [heq] at h1
    have h12 : s₁⁻¹ * s₂ ∈ V := by
      have e : ((σ s₂)⁻¹ * (h * s₁))⁻¹ * ((σ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ := by group
      rw [← e]
      exact V.mul_mem (V.inv_mem h1) (hσV s₂ hs₂)
    obtain ⟨u, _, hu⟩ := hT s₂ (hS s₂ hs₂)
    have e1 : s₁ = u := hu s₁ ⟨hs₁, h12⟩
    have e2 : s₂ = u := hu s₂ ⟨hs₂, by rw [inv_mul_cancel]; exact V.one_mem⟩
    rw [e1, e2]
  have himg : S.image σ = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact hσS s hs
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ s ∈ S, f (σ s) = ∑ x ∈ S.image σ, f x := (Finset.sum_image hinj).symm
    _ = ∑ s ∈ S, f s := by rw [himg]

theorem main {G : Type u_1} {C : Type u_2} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* C ≃+* C) (hn : ∀ (g : G) (y : C), ‖act g y‖ = ‖y‖)
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (a b : C) (hb : ‖b‖ ≤ (1 : ℝ))
    (hV : ∀ g ∈ V, act g b = b) (ha : ∑ s ∈ S, act s b = a) (c : G → C)
    (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h)) (t ε : ℝ) (ht : (0 : ℝ) ≤ t)
    (hε : (0 : ℝ) ≤ ε) (hct : ∀ g ∈ H, ‖c g‖ ≤ t) (hcε : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  classical
  refine ⟨-∑ s ∈ S, act s b * c s, ?_, ?_⟩
  · rw [norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ht
    intro s hs
    rw [norm_mul, hn]
    calc ‖b‖ * ‖c s‖ ≤ 1 * t := mul_le_mul hb (hct s (hS s hs)) (norm_nonneg _) zero_le_one
      _ = t := one_mul t
  · intro h hh
    obtain ⟨σ, hσ, hsum⟩ := exists_perm (C := C) H V S hS hT h hh
    have hmul : ∀ (g k : G) (y : C), act (g * k) y = act g (act k y) := by
      intro g k y
      rw [map_mul]
      rfl

    have hterm : ∀ s ∈ S, act h (act s b * c s) = act (σ s) b * c (σ s)
        + act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - act (σ s) b * c h := by
      intro s hs
      have hsH := hS s hs
      have hσH := hS (σ s) (hσ s hs).1
      have hvV := (hσ s hs).2
      have hhs : h * s = σ s * ((σ s)⁻¹ * (h * s)) := (mul_inv_cancel_left _ _).symm
      have hvH : (σ s)⁻¹ * (h * s) ∈ H := H.mul_mem (H.inv_mem hσH) (H.mul_mem hh hsH)
      have h1 : act h (act s b) = act (σ s) b := by
        rw [← hmul, hhs, hmul, hV _ hvV]
      have h2 : act h (c s) = c (σ s) + act (σ s) (c ((σ s)⁻¹ * (h * s))) - c h := by
        have e1 := hc h hh s hsH
        have e2 := hc (σ s) hσH _ hvH
        rw [← hhs] at e2
        linear_combination e2 - e1
      rw [map_mul, h1, h2, map_mul (act (σ s)) b (c ((σ s)⁻¹ * (h * s)))]
      ring
    have hsumA : ∑ s ∈ S, act (σ s) b = a := by
      rw [← ha]
      exact hsum (fun g => act g b)
    have hsumT : ∑ s ∈ S, act (σ s) b * c (σ s) = ∑ s ∈ S, act s b * c s :=
      hsum (fun g => act g b * c g)
    have hact : act h (-∑ s ∈ S, act s b * c s) = -(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h) := by
      rw [map_neg, map_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hsumT, ← Finset.sum_mul, hsumA]
    rw [hact]
    have hE : a * c h - (-(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h)
        - -∑ s ∈ S, act s b * c s) = ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) := by
      ring
    rw [hE]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε
    intro s hs
    rw [hn, norm_mul]
    have hvH : (σ s)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hσ s hs).1)) (H.mul_mem hh (hS s hs))
    calc ‖b‖ * ‖c ((σ s)⁻¹ * (h * s))‖ ≤ 1 * ε :=
          mul_le_mul hb (hcε _ hvH (hσ s hs).2) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

end GlobalTheory.PermutationExistence
