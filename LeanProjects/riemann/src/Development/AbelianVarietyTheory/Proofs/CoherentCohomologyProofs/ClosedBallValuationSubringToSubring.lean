import Mathlib

namespace GlobalTheory.ClosedBallValuationSubring

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

def closedBallSubring : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

def closedBallValuationSubring : ValuationSubring K where
  toSubring := closedBallSubring K
  mem_or_inv_mem' := by
    intro x
    change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · right
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

def openBallIdeal : Ideal (closedBallSubring K) where
  carrier := {x | ‖(x : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max (a : K) (b : K)).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hc : ‖(c : K)‖ ≤ 1 := c.2
    change ‖(c : K) * (x : K)‖ < 1
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc (norm_nonneg _) hx

variable {K}

theorem mem_closedBallSubring {x : K} : x ∈ closedBallSubring K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem mem_openBallIdeal {x : closedBallSubring K} :
    x ∈ openBallIdeal K ↔ ‖(x : K)‖ < 1 := Iff.rfl

theorem isUnit_iff_norm_eq_one {x : closedBallSubring K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hu : ‖((u : closedBallSubring K) : K)‖ ≤ 1 := (u : closedBallSubring K).2
    have hv : ‖((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).1‖ ≤ 1 :=
      ((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).2
    have hprod : ‖((u : closedBallSubring K) : K)‖ *
        ‖((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).1‖ = 1 := by
      rw [← norm_mul]
      have h := congrArg Subtype.val u.mul_inv
      simp only [Subring.coe_mul, Subring.coe_one] at h
      rw [h, norm_one]
    refine le_antisymm hu ?_
    calc (1 : ℝ) = _ := hprod.symm
      _ ≤ ‖((u : closedBallSubring K) : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    have hinv : (x : K)⁻¹ ∈ closedBallSubring K := by
      rw [mem_closedBallSubring, norm_inv, h, inv_one]
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : K)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_one]
    exact mul_inv_cancel₀ hx0

theorem mem_openBallIdeal_iff_not_isUnit {x : closedBallSubring K} :
    x ∈ openBallIdeal K ↔ ¬ IsUnit x := by
  rw [mem_openBallIdeal, isUnit_iff_norm_eq_one]
  have hle : ‖(x : K)‖ ≤ 1 := mem_closedBallSubring.mp x.2
  exact ⟨fun h he => (ne_of_lt h) he, fun h => lt_of_le_of_ne hle h⟩

variable (K)

instance isLocalRing_closedBallSubring : IsLocalRing (closedBallSubring K) :=
  inferInstanceAs (IsLocalRing (closedBallValuationSubring K))

theorem openBallIdeal_eq_maximalIdeal :
    openBallIdeal K = IsLocalRing.maximalIdeal (closedBallSubring K) := by
  ext x
  rw [mem_openBallIdeal_iff_not_isUnit, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem openBallIdeal_isMaximal : (openBallIdeal K).IsMaximal := by
  rw [openBallIdeal_eq_maximalIdeal]
  exact IsLocalRing.maximalIdeal.isMaximal _

end GlobalTheory.ClosedBallValuationSubring
