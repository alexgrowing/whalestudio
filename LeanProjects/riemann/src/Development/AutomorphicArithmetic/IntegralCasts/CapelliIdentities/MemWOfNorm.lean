import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.kb :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ AlgebraicClosure (ZMod p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.WW :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ WittVector p (UpperTheory.Reformulated.B.Qi32.kb p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.K0 :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ FractionRing (UpperTheory.Reformulated.B.Qi32.WW p)

theorem UpperTheory.Reformulated.B.Qi32.mem_W_of_norm :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (i0 : UpperTheory.Reformulated.B.Qi32.K0 p →+* ℂ_[p]),
      (∀ (x : UpperTheory.Reformulated.B.Qi32.WW p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p])
                ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  x)‖ ≤
            (1 : ℝ)) →
        ∀ (x : UpperTheory.Reformulated.B.Qi32.K0 p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p]) x‖ ≤ (1 : ℝ) →
            ∃ (w : UpperTheory.Reformulated.B.Qi32.WW p),
              (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  w =
                x := by
  intro p inst i0 hW x hx
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
    rw [h, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rcases ValuationRing.isInteger_or_isInteger (UpperTheory.Reformulated.B.Qi32.WW p) x with h | ⟨w, hw⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, map_zero _⟩
  by_cases hu : IsUnit w
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : (UpperTheory.Reformulated.B.Qi32.WW p)ˣ) : UpperTheory.Reformulated.B.Qi32.WW p), ?_⟩
    rw [map_units_inv, hw, inv_inv]
  · exfalso
    have hirr : Irreducible (p : UpperTheory.Reformulated.B.Qi32.WW p) := WittVector.irreducible p
    have hmem : w ∈ IsLocalRing.maximalIdeal (UpperTheory.Reformulated.B.Qi32.WW p) := hu
    rw [hirr.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨v, rfl⟩ := hmem
    have h1 : ‖i0 x‖ * ‖i0 x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
    have h2 : ‖i0 x⁻¹‖ < 1 := by
      rw [← hw, map_mul, map_mul, map_natCast, map_natCast, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hW v)) hp
    have h3 : ‖i0 x‖ * ‖i0 x⁻¹‖ ≤ ‖i0 x⁻¹‖ := mul_le_of_le_one_left (norm_nonneg _) hx
    linarith
