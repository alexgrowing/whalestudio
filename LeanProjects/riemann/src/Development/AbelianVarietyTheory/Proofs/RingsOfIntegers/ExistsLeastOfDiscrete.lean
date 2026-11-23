import Mathlib

namespace GlobalTheory.ValuedPrincipal

variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem exists_val_eq {x : F} (hx : x ≠ 0) :
    ∃ r : ℚ, v x = (r : WithTop ℚ) ∧ v x⁻¹ = ((-r : ℚ) : WithTop ℚ) := by
  have hit : v x⁻¹ ≠ ⊤ := (v.ne_top_iff).2 (inv_ne_zero hx)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((v.ne_top_iff).2 hx)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hit
  refine ⟨r, hr.symm, ?_⟩
  have hsum : v x + v x⁻¹ = 0 := by
    rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  rw [← hr, ← hs, ← WithTop.coe_add] at hsum
  have h0 : r + s = 0 := by exact_mod_cast hsum
  rw [← hs]
  congr 1
  linarith

theorem exists_val_eq_int {π : F} (hπ : v π = ((1 : ℚ) : WithTop ℚ)) (n : ℤ) :
    ∃ y : F, y ≠ 0 ∧ v y = ((n : ℚ) : WithTop ℚ) := by
  have hπ0 : π ≠ 0 := (v.ne_top_iff).1 (by rw [hπ]; exact WithTop.coe_ne_top)
  obtain ⟨r, hr, hri⟩ := exists_val_eq v hπ0
  have hr1 : r = 1 := by
    rw [hπ] at hr
    exact_mod_cast hr.symm
  subst hr1
  induction n using Int.induction_on with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨y * π, mul_ne_zero hy hπ0, ?_⟩
    rw [v.map_mul, hyv, hπ, ← WithTop.coe_add]
    congr 1
    push_cast
    ring
  | pred k ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨y * π⁻¹, mul_ne_zero hy (inv_ne_zero hπ0), ?_⟩
    rw [v.map_mul, hyv, hri, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

theorem val_pow_eq {t : F} {r : ℚ} (h : v t = (r : WithTop ℚ)) (k : ℕ) :
    v (t ^ k) = (((k : ℚ) * r : ℚ) : WithTop ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, v.map_mul, ih, h, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

theorem exists_val_eq_rat [IsAlgClosed F] {π : F} (hπ : v π = ((1 : ℚ) : WithTop ℚ)) (q : ℚ) :
    ∃ t : F, t ≠ 0 ∧ v t = (q : WithTop ℚ) := by
  obtain ⟨y, hy, hyv⟩ := exists_val_eq_int v hπ q.num
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq y q.den_pos
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_ne_zero] at ht
    exact hy ht.symm
  obtain ⟨s, hs, -⟩ := exists_val_eq v ht0
  refine ⟨t, ht0, ?_⟩
  have hp := val_pow_eq v hs q.den
  rw [ht, hyv] at hp
  have hq : (q.num : ℚ) = q.den * s := by exact_mod_cast hp
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [hs]
  congr 1
  rw [← Rat.num_div_den q, eq_div_iff hd, hq]
  ring

theorem exists_least_of_discrete {π : F} (hπ : v π = ((1 : ℚ) : WithTop ℚ)) {d : ℕ} (hd : 1 ≤ d)
    (h : ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) (q : ℚ) :
    ∃ t : F, t ≠ 0 ∧ (q : WithTop ℚ) ≤ v t ∧ ∀ a : F, (q : WithTop ℚ) ≤ v a → v t ≤ v a := by
  classical
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hne : ∃ n : ℤ, ∃ x : F, x ≠ 0 ∧ v x = (((n : ℚ) / d : ℚ) : WithTop ℚ) ∧ q ≤ (n : ℚ) / d := by
    obtain ⟨y, hy, hyv⟩ := exists_val_eq_int v hπ ⌈q⌉
    have hc : ((⌈q⌉ * d : ℤ) : ℚ) / d = ⌈q⌉ := by
      push_cast
      field_simp
    refine ⟨⌈q⌉ * d, y, hy, ?_, ?_⟩
    · rw [hyv, hc]
    · rw [hc]
      exact Int.le_ceil q
  have hbdd : ∃ b : ℤ, ∀ n : ℤ, (∃ x : F, x ≠ 0 ∧ v x = (((n : ℚ) / d : ℚ) : WithTop ℚ) ∧
      q ≤ (n : ℚ) / d) → b ≤ n := by
    refine ⟨⌊q * d⌋, ?_⟩
    rintro n ⟨x, -, -, hqn⟩
    rw [le_div_iff₀ hdq] at hqn
    have hf := Int.floor_le (q * d)
    exact_mod_cast hf.trans hqn
  obtain ⟨n, ⟨t, ht, htv, hqt⟩, hmin⟩ := Int.exists_least_of_bdd hbdd hne
  refine ⟨t, ht, ?_, ?_⟩
  · rw [htv]
    exact_mod_cast hqt
  · intro a ha
    by_cases ha0 : a = 0
    · rw [ha0, v.map_zero]
      exact le_top
    · obtain ⟨m, hm⟩ := h a ha0
      have hqm : q ≤ (m : ℚ) / d := by
        rw [hm] at ha
        exact_mod_cast ha
      have hnm : (n : ℚ) ≤ m := by exact_mod_cast hmin m ⟨a, ha0, hm, hqm⟩
      have hdiv : (n : ℚ) / d ≤ (m : ℚ) / d := by gcongr
      rw [htv, hm]
      exact_mod_cast hdiv

theorem exists_eq_mul_of_le {t a : F} (ht : t ≠ 0) (h : v t ≤ v a) :
    ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ a = c * t := by
  refine ⟨a * t⁻¹, ?_, (inv_mul_cancel_right₀ ht a).symm⟩
  by_cases ha : a = 0
  · rw [ha, zero_mul, v.map_zero]
    exact le_top
  · obtain ⟨r, hr, hri⟩ := exists_val_eq v ht
    obtain ⟨s, hs, -⟩ := exists_val_eq v ha
    rw [hr, hs] at h
    have hrs : r ≤ s := by exact_mod_cast h
    rw [v.map_mul, hs, hri, ← WithTop.coe_add]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ s + -r)

theorem main : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (π : F), v π = ((1 : ℚ) : WithTop ℚ) → (IsAlgClosed F ∨ ∃ d : ℕ, 1 ≤ d ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) → ∀ q : ℚ, ∃ t : F, t ≠ 0 ∧ ((q : ℚ) : WithTop ℚ) ≤ v t ∧ ∀ a : F, ((q : ℚ) : WithTop ℚ) ≤ v a → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ a = c * t := by
  intro F _ v π hπ hcase q
  have key : ∃ t : F, t ≠ 0 ∧ (q : WithTop ℚ) ≤ v t ∧
      ∀ a : F, (q : WithTop ℚ) ≤ v a → v t ≤ v a := by
    rcases hcase with hac | ⟨d, hd, hdisc⟩
    · haveI := hac
      obtain ⟨t, ht, htv⟩ := exists_val_eq_rat v hπ q
      refine ⟨t, ht, htv.ge, fun a ha => ?_⟩
      rw [htv]
      exact ha
    · exact exists_least_of_discrete v hπ hd hdisc q
  obtain ⟨t, ht, hqt, hmin⟩ := key
  exact ⟨t, ht, hqt, fun a ha => exists_eq_mul_of_le v ht (hmin a ha)⟩

end GlobalTheory.ValuedPrincipal
