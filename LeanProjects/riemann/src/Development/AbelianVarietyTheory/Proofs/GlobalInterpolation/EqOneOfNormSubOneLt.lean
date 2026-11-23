import Mathlib

namespace GlobalTheory.CharacterConductorBall

private lemma norm_sub_one_le_norm_mul_self_sub_one (w : ℂ) (h : ‖w - 1‖ < 1 / 2) :
    3 / 2 * ‖w - 1‖ ≤ ‖w * w - 1‖ := by
  have h1 : w * w - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (2 : ℝ) ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have := norm_sub_le (w + 1) (w - 1)
    have e : (w + 1) - (w - 1) = (2 : ℂ) := by ring
    rw [e] at this
    simpa using this
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem eq_one_of_norm_sub_one_lt {A : Type} [AddMonoid A] (ψ : AddChar A ℂ) (B : Set A)
    (hB : ∀ x ∈ B, x + x ∈ B) (hψ : ∀ x ∈ B, ‖ψ x - 1‖ < 1 / 2) : ∀ x ∈ B, ψ x = 1 := by

  have key : ∀ k : ℕ, ∀ x ∈ B, (3 / 2 : ℝ) ^ k * ‖ψ x - 1‖ < 1 / 2 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hψ x hx
    | succ k ih =>
      intro x hx
      have h2 := ih (x + x) (hB x hx)
      have h3 := norm_sub_one_le_norm_mul_self_sub_one (ψ x) (hψ x hx)
      rw [AddChar.map_add_eq_mul] at h2
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖ψ x - 1‖ = (3 / 2) ^ k * (3 / 2 * ‖ψ x - 1‖) := by ring
        _ ≤ (3 / 2) ^ k * ‖ψ x * ψ x - 1‖ := by gcongr
        _ < 1 / 2 := h2
  intro x hx
  by_contra hne
  have hpos : 0 < ‖ψ x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖ψ x - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have := key k x hx
  rw [div_lt_iff₀ hpos] at hk
  linarith

theorem exists_ball_trivial {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by

  have hnhds : (ψ : K → ℂ) ⁻¹' {w : ℂ | ‖w - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hnhds
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hc0 : c ≠ 0 := by
    have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.2 γ.ne_zero)
    rw [map_zero] at this
    exact this.ne'

  have hlt : ∀ y ∈ {y : K | Valued.v y < c}, ψ y = 1 := by
    refine eq_one_of_norm_sub_one_lt ψ _ (fun y hy => ?_) (fun y hy => ?_)
    · exact lt_of_le_of_lt ((Valued.v.map_add y y).trans (max_self _).le) hy
    · apply hγ
      simpa [Valuation.restrict_lt_iff_lt_embedding] using hy
  refine ⟨WithZero.log c - 1, fun x hx => hlt x ?_⟩
  calc Valued.v x ≤ WithZero.exp (WithZero.log c - 1) := hx
    _ < WithZero.exp (WithZero.log c) := WithZero.exp_lt_exp.2 (by omega)
    _ = c := WithZero.exp_log hc0

private lemma addChar_trivial_mul_of_valuation_le {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) {t t' : K}
    (ht : ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1)
    (hle : Valued.v t' ≤ Valued.v t) :
    ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t' * s) = 1 := by
  intro s hs
  by_cases h0 : t = 0
  · subst h0
    have : t' = 0 := by simpa using hle
    simp [this, AddChar.map_zero_eq_one]
  · have hv : Valued.v t ≠ 0 := by simpa using h0
    have e : t' * s = t * (t' * t⁻¹ * s) := by field_simp
    rw [e]
    apply ht
    rw [map_mul, map_mul, map_inv₀]
    calc Valued.v t' * (Valued.v t)⁻¹ * Valued.v s ≤ Valued.v t * (Valued.v t)⁻¹ * 1 := by
          gcongr
      _ = 1 := by rw [mul_one, mul_inv_cancel₀ hv]

theorem exists_conductor {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) (hψ : ∃ t : K, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K,
      (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
        Valued.v t ≤ WithZero.exp n := by
  classical
  obtain ⟨m, hm⟩ := exists_ball_trivial ψ hc
  obtain ⟨t₀, ht₀⟩ := hψ
  have ht₀0 : t₀ ≠ 0 := by rintro rfl; simp [AddChar.map_zero_eq_one] at ht₀
  have hnot : ¬ ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t₀ * s) = 1 :=
    fun h => ht₀ (by simpa using h 1 (by simp))

  have hmem : ∀ t : K, Valued.v t ≤ WithZero.exp m →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1 := by
    intro t ht s hs
    apply hm
    rw [map_mul]
    calc Valued.v t * Valued.v s ≤ WithZero.exp m * 1 := by gcongr
      _ = WithZero.exp m := mul_one _
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, (∀ t : K, Valued.v t ≤ WithZero.exp k →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) → k ≤ b := by
    refine ⟨WithZero.log (Valued.v t₀), fun k hk => ?_⟩
    by_contra hlt
    apply hnot
    apply hk
    have hv : Valued.v t₀ ≠ 0 := by simpa using ht₀0
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 (by omega)
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨m, hmem⟩
  refine ⟨n, fun t => ⟨fun hS => ?_, fun ht => hn t ht⟩⟩
  by_contra hgt
  rw [not_le] at hgt
  have hv : Valued.v t ≠ 0 := ne_of_gt (lt_trans WithZero.exp_pos hgt)
  have hj : WithZero.log (Valued.v t) ≤ n := by
    apply hmax
    intro t' ht'
    rw [WithZero.exp_log hv] at ht'
    exact addChar_trivial_mul_of_valuation_le ψ hS ht'
  have : Valued.v t ≤ WithZero.exp n := by
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 hj
  exact absurd hgt (not_lt.2 this)

end GlobalTheory.CharacterConductorBall
