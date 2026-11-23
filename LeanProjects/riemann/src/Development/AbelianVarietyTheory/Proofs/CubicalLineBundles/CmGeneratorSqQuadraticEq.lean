import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open NumberField

namespace GlobalTheory.CMGeneratorSquare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cm_generator_sq_quadratic_eq (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.w0 * H.w0 = H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  have hd : (H.d + 1) = 4 * ((H.d + 1) / 4) := by
    have := H.d_mod; omega
  have h1 : (4 : 𝓞 E) * (H.w0 * H.w0) = 4 * (H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E)) := by
    have h2 := H.two_weight_eq_one_add_root
    have h3 := H.rt_sq
    have h4 : ((H.d + 1 : ℕ) : 𝓞 E) = 4 * (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
      conv_lhs => rw [hd]
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have h5 : (4 : 𝓞 E) * (H.w0 * H.w0) = (2 * H.w0) ^ 2 := by ring
    rw [h5, h2, mul_sub, ← h4]
    push_cast
    linear_combination h3 - 2 * h2
  have h4ne : (4 : 𝓞 E) ≠ 0 := by exact_mod_cast (by norm_num : (4 : ℕ) ≠ 0)
  exact mul_left_cancel₀ h4ne h1

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E}, a ∈ GlobalTheory.CM.OK H →
    ∃ (u : ℤ) (v : ℤ), a = (↑u : NumberField.RingOfIntegers E) + (↑v : NumberField.RingOfIntegers E) *
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  set k : ℤ := (((H.d + 1) / 4 : ℕ) : ℤ) with hk
  have hsq : H.w0 * H.w0 = H.w0 - (k : 𝓞 E) := by rw [cm_generator_sq_quadratic_eq H, hk, Int.cast_natCast]
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - v * v' * k, u * v' + v * u' + v * v', ?_⟩
    push_cast
    linear_combination (v * v' : 𝓞 E) * hsq

end GlobalTheory.CMGeneratorSquare
