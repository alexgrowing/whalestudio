import Mathlib

open Set

namespace ReciprocityTheory.Cheb

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def latSumEquiv (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂) :
    Λ' × reps ≃ Λ₀ :=
  Equiv.ofBijective (fun p => ⟨(p.1 : V) + (p.2 : V), Λ₀.add_mem (hle p.1.2) (hmem _ p.2.2)⟩) (by
    constructor
    · rintro ⟨l₁, β₁⟩ ⟨l₂, β₂⟩ h
      simp only [Subtype.mk.injEq] at h
      have hβ : (β₁ : V) = β₂ := huniq _ β₁.2 _ β₂.2 (by
        have e : (β₁ : V) - β₂ = l₂ - l₁ := by
          rw [sub_eq_sub_iff_add_eq_add, add_comm (β₁ : V), h]
        rw [e]; exact Λ'.sub_mem l₂.2 l₁.2)
      have hl : (l₁ : V) = l₂ := by rw [hβ] at h; exact add_right_cancel h
      exact Prod.ext (Subtype.ext hl) (Subtype.ext hβ)
    · rintro ⟨α, hα⟩
      obtain ⟨l, hl, β, hβ, rfl⟩ := hcover α hα
      exact ⟨(⟨l, hl⟩, ⟨β, hβ⟩), rfl⟩)

theorem tsum_latSum_eq (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (g : V → ℂ) (hg : Summable fun α : Λ₀ => g α) :
    ∑' α : Λ₀, c' α * g α = ∑' l : Λ', ∑ β ∈ reps, c' β * (g (l + β) - g l) := by
  set e := latSumEquiv Λ₀ Λ' hle reps hmem hcover huniq
  have hc : ∀ α : Λ₀, ‖c' α‖ ≤ ∑ β ∈ reps, ‖c' β‖ := by
    rintro ⟨α, hα⟩
    obtain ⟨l, hl, β, hβ, rfl⟩ := hcover α hα
    rw [hper l hl β hβ]
    exact Finset.single_le_sum (f := fun β => ‖c' β‖) (fun _ _ => norm_nonneg _) hβ
  have hcg : Summable fun α : Λ₀ => c' α * g α := by
    refine summable_norm_iff.mp (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => ?_)
      ((summable_norm_iff.mpr hg).mul_left (∑ β ∈ reps, ‖c' β‖)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc α) (norm_nonneg _)
  have hs : Summable fun p : Λ' × reps => c' (e p) * g (e p) := (e.summable_iff).mpr hcg
  rw [← e.tsum_eq, hs.tsum_prod]
  refine tsum_congr fun l => ?_
  rw [tsum_fintype]
  have h1 : ∀ β : reps, (fun α : Λ₀ => c' α * g α) (e (l, β)) = c' β * g (l + β) := by
    rintro ⟨β, hβ⟩
    show c' ((l : V) + β) * g ((l : V) + β) = _
    rw [hper l l.2 β hβ]
  simp only [h1]
  rw [Finset.sum_coe_sort reps (fun β => c' β * g (l + β))]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmean, zero_mul, sub_zero]

variable [FiniteDimensional ℝ V]

theorem exists_continuousOn_latticeSum (Λ₀ Λ' : Submodule ℤ V) [DiscreteTopology Λ₀] (hle : Λ' ≤ Λ₀)
    (reps : Finset V) (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂)
    (c' : V → ℂ) (hper : ∀ l ∈ Λ', ∀ β ∈ reps, c' (l + β) = c' β) (hmean : ∑ β ∈ reps, c' β = 0)
    (G : ℝ → V → ℂ) (r : ℝ) (hr : r < -(Module.finrank ℤ Λ₀ : ℝ))
    (hdiff : ∃ R₀ C : ℝ, ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ Λ', R₀ ≤ ‖x‖ →
      ‖G s (x + β) - G s x‖ ≤ C * ‖x‖ ^ r)
    (K : ℝ) (hbound : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ Λ₀, ‖G s x‖ ≤ K)
    (hsum : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : Λ₀ => G s α)
    (hcont : ∀ x ∈ Λ₀, ContinuousOn (fun s => G s x) (Icc 1 2)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, F s = ∑' α : Λ₀, c' α * G s α := by
  classical
  obtain ⟨R₀, C, hRC⟩ := hdiff
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set A := ∑ β ∈ reps, ‖c' β‖ with hAdef
  have hr0 : r < 0 := lt_of_lt_of_le hr (neg_nonpos.mpr (Nat.cast_nonneg _))
  set X := |C| + 2 * |K| * R ^ (-r) with hXdef
  have hX : 0 ≤ X := by positivity
  let u : Λ' → ℝ := fun l => A * X * ‖(l : V)‖ ^ r + if (l : V) = 0 then A * (2 * |K|) else 0
  have hu : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.mul_left (A * X) ?_
      have h0 := ZLattice.summable_norm_rpow Λ₀ r hr
      have h1 := h0.comp_injective (i := fun l : Λ' => (⟨l, hle l.2⟩ : Λ₀))
        (fun a b h => Subtype.ext (congrArg Subtype.val h :))
      exact h1
    · apply summable_of_ne_finset_zero (s := {0})
      intro l hl
      have : (l : V) ≠ 0 := by simpa using hl
      simp [this]
  refine ⟨fun s => ∑' l : Λ', ∑ β ∈ reps, c' β * (G s (l + β) - G s l), ?_, ?_⟩
  · refine continuousOn_tsum (u := u) (fun l => ?_) hu (fun l s hs => ?_)
    · refine continuousOn_finsetSum _ fun β hβ => ?_
      exact continuousOn_const.mul
        ((hcont _ (Λ₀.add_mem (hle l.2) (hmem β hβ))).sub (hcont _ (hle l.2)))
    · have key : ∀ β ∈ reps, ‖G s (l + β) - G s l‖ ≤
          X * ‖(l : V)‖ ^ r + if (l : V) = 0 then 2 * |K| else 0 := by
        intro β hβ
        have h2K : ‖G s (l + β) - G s l‖ ≤ 2 * |K| := by
          refine (norm_sub_le _ _).trans ?_
          have := hbound s hs _ (Λ₀.add_mem (hle l.2) (hmem β hβ))
          have := hbound s hs _ (hle l.2)
          have := le_abs_self K
          linarith
        have hpow : 0 ≤ ‖(l : V)‖ ^ r := Real.rpow_nonneg (norm_nonneg _) _
        by_cases hl0 : (l : V) = 0
        · rw [if_pos hl0]
          nlinarith
        rw [if_neg hl0, add_zero]
        by_cases hR : R ≤ ‖(l : V)‖
        · have := hRC s hs β hβ l l.2 ((le_max_left _ _).trans hR)
          have hC : C * ‖(l : V)‖ ^ r ≤ |C| * ‖(l : V)‖ ^ r :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hpow
          have : 0 ≤ 2 * |K| * R ^ (-r) * ‖(l : V)‖ ^ r := by positivity
          nlinarith
        · rw [not_le] at hR
          have hlpos : 0 < ‖(l : V)‖ := norm_pos_iff.mpr hl0
          have hRr : R ^ r ≤ ‖(l : V)‖ ^ r := Real.rpow_le_rpow_of_nonpos hlpos hR.le hr0.le
          have hone : R ^ (-r) * R ^ r = 1 := by
            rw [Real.rpow_neg hRpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hRpos r).ne']
          have hRn : 0 ≤ R ^ (-r) := Real.rpow_nonneg hRpos.le _
          have h3 : 2 * |K| ≤ 2 * |K| * R ^ (-r) * ‖(l : V)‖ ^ r := by
            calc 2 * |K| = 2 * |K| * (R ^ (-r) * R ^ r) := by rw [hone, mul_one]
              _ ≤ 2 * |K| * (R ^ (-r) * ‖(l : V)‖ ^ r) := by gcongr
              _ = _ := by ring
          have : 0 ≤ |C| * ‖(l : V)‖ ^ r := by positivity
          nlinarith
      calc ‖∑ β ∈ reps, c' β * (G s (l + β) - G s l)‖
          ≤ ∑ β ∈ reps, ‖c' β‖ * ‖G s (l + β) - G s l‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp only [norm_mul]
        _ ≤ ∑ β ∈ reps, ‖c' β‖ * (X * ‖(l : V)‖ ^ r + if (l : V) = 0 then 2 * |K| else 0) :=
            Finset.sum_le_sum fun β hβ => mul_le_mul_of_nonneg_left (key β hβ) (norm_nonneg _)
        _ = u l := by
            rw [← Finset.sum_mul]
            simp only [u]
            split_ifs <;> ring
  · intro s hs
    exact (tsum_latSum_eq Λ₀ Λ' hle reps hmem hcover huniq c' hper hmean (G s) (hsum s hs)).symm

end ReciprocityTheory.Cheb
