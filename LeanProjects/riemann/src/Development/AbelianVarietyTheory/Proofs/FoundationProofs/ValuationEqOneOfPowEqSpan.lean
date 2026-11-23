import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem valuation_eq_one_of_pow_eq_span :
    ∀ (E Ω R : Type) [Field E] [Field Ω] [Algebra E Ω] [CommRing R] [Algebra R E] (B : ValuationSubring Ω)
      (J : Submodule R E) (N : ℕ), 0 < N → (∀ x : R, algebraMap E Ω (algebraMap R E x) ∈ B) → ∀ w : E, w ≠ 0 →
      (J ^ N = Submodule.span R {w}) → ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / c ^ N)) = 1 := by
  intro E Ω R _ _ _ _ _ B J N hN hRB w hw hJ
  set v := B.valuation.comap (algebraMap E Ω) with hv
  have hva : ∀ x, v x = B.valuation (algebraMap E Ω x) := fun x => rfl
  have hR : ∀ r : R, v (algebraMap R E r) ≤ 1 := fun r => by
    rw [hva]; exact (B.valuation_le_one_iff _).mpr (hRB r)
  have hsm : ∀ (r : R) (z : E), v (r • z) ≤ v z := fun r z => by
    rw [Algebra.smul_def, v.map_mul]
    calc v (algebraMap R E r) * v z ≤ 1 * v z := mul_le_mul' (hR r) le_rfl
      _ = v z := one_mul _
  let S : ℕ → Submodule R E := fun n =>
    { carrier := {z | ∃ c ∈ J, v z ≤ v c ^ (n + 1)}
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      add_mem' := by
        rintro z₁ z₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
        rcases le_total (v c₁) (v c₂) with h | h
        · refine ⟨c₂, hc₂, (v.map_add z₁ z₂).trans (max_le ?_ h₂)⟩
          exact h₁.trans (pow_le_pow_left₀ zero_le' h _)
        · refine ⟨c₁, hc₁, (v.map_add z₁ z₂).trans (max_le h₁ ?_)⟩
          exact h₂.trans (pow_le_pow_left₀ zero_le' h _)
      smul_mem' := by
        rintro r z ⟨c, hc, h⟩
        exact ⟨c, hc, (hsm r z).trans h⟩ }
  have key : ∀ n : ℕ, J ^ (n + 1) ≤ S n := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [pow_one] at hz
      exact ⟨z, hz, by simp⟩
    | succ n ih =>
      rw [pow_succ]
      refine Submodule.mul_le.mpr ?_
      intro y hy z' hz'
      obtain ⟨c, hc, h⟩ := ih hy
      show ∃ c ∈ J, v (y * z') ≤ v c ^ (n + 1 + 1)
      rw [v.map_mul]
      rcases le_total (v c) (v z') with h' | h'
      · refine ⟨z', hz', ?_⟩
        rw [pow_succ]
        exact mul_le_mul' (h.trans (pow_le_pow_left₀ zero_le' h' _)) le_rfl
      · refine ⟨c, hc, ?_⟩
        rw [pow_succ]
        exact mul_le_mul' h h'
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hwmem : w ∈ J ^ (n + 1) := by rw [hJ]; exact Submodule.mem_span_singleton_self w
  obtain ⟨c, hc, hle⟩ := key n hwmem
  have hcN : c ^ (n + 1) ∈ Submodule.span R {w} := hJ ▸ Submodule.pow_mem_pow J hc (n + 1)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hcN
  have hge : v (c ^ (n + 1)) ≤ v w := by
    rw [← hr]; exact hsm r w
  have heq : v (c ^ (n + 1)) = v w := le_antisymm hge (by rw [v.map_pow]; exact hle)
  have hw0 : v w ≠ 0 := by
    rw [hva]; exact (Valuation.ne_zero_iff _).mpr ((_root_.map_ne_zero _).mpr hw)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw0
    rw [← heq]; simp
  refine ⟨c, hc0, ?_⟩
  have : v (w / c ^ (n + 1)) = 1 := by
    rw [map_div₀, heq, div_self hw0]
  simpa [hva] using this

end GlobalTheory
