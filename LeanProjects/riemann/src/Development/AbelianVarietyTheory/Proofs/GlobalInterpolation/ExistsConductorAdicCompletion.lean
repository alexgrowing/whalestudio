import Mathlib

namespace GlobalTheory.ConductorAdicCompletion

theorem eq_one_of_pow_near_one (z : ℂ) (h : ∀ k : ℕ, ‖z ^ k - 1‖ ≤ 1 / 2) : z = 1 := by
  by_contra hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1

  have hre : ∀ k : ℕ, 1 / 2 ≤ (z ^ k).re := by
    intro k
    have h2 := (Complex.abs_re_le_norm (z ^ k - 1)).trans (h k)
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.mp h2).1
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hsum : ∑ k ∈ Finset.range N, z ^ k = (z ^ N - 1) / (z - 1) := geom_sum_eq hz N
  have hlow : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, z ^ k).re := by
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ k ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hre k
  have hup : (∑ k ∈ Finset.range N, z ^ k).re ≤ 1 / 2 / ‖z - 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [hsum, norm_div]
    exact div_le_div_of_nonneg_right (h N) (norm_nonneg _)
  have he : 1 / 2 / ‖z - 1‖ = (1 / ‖z - 1‖) / 2 := by ring
  linarith

theorem exists_ball_trivial {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by
  have hmem : {x : K | ‖ψ x - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) continuous_const
    · simp
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hmem
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).mpr γ.ne_zero
  refine ⟨WithZero.log g - 1, fun x hx => ?_⟩
  have hlt : WithZero.exp (WithZero.log g - 1) < g :=
    (WithZero.lt_log_iff_exp_lt hg0).mp (by omega)
  apply eq_one_of_pow_near_one
  intro k
  rw [← AddChar.map_nsmul_eq_pow]
  have hk : Valued.v (k • x) ≤ WithZero.exp (WithZero.log g - 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_le _ ih hx
  have : k • x ∈ {x : K | ‖ψ x - 1‖ < 1 / 2} := by
    apply hγ
    exact (Valuation.restrict_lt_iff_lt_embedding _).mpr (hk.trans_lt hlt)
  exact le_of_lt this

theorem exists_conductor {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m : ℤ => ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1)
    ⟨WithZero.log (Valued.v t₀ : WithZero (Multiplicative ℤ)), fun m hm => by
      have h1 : WithZero.exp m < Valued.v t₀ := lt_of_not_ge fun h => ht₀ (hm _ h)
      exact ((WithZero.lt_log_iff_exp_lt (ne_zero_of_lt h1)).mpr h1).le⟩
    (exists_ball_trivial ψ hc)
  refine ⟨n, fun t => ⟨fun h => ?_, fun h s hs => ?_⟩⟩
  · by_contra hlt
    have h1 : WithZero.exp n < Valued.v t := lt_of_not_ge hlt
    have hv0 : (Valued.v t : WithZero (Multiplicative ℤ)) ≠ 0 := ne_zero_of_lt h1
    have ht : t ≠ 0 := fun h0 => hv0 (by simp [h0])
    have h2 := (WithZero.lt_log_iff_exp_lt hv0).mpr h1
    have h3 := hmax (WithZero.log (Valued.v t : WithZero (Multiplicative ℤ))) (fun x hx => by
      rw [WithZero.exp_log hv0] at hx
      have h4 := h (x / t) (by
        rw [map_div₀]
        exact div_le_one_of_le₀ hx zero_le)
      rwa [mul_div_cancel₀ _ ht] at h4)
    omega
  · apply hn
    rw [map_mul]
    exact (mul_le_of_le_one_right' hs).trans h

theorem exists_conductor_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (ψ : AddChar (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ℂ),
      Continuous (⇑ψ : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → ℂ) →
      (∀ t, ‖ψ t‖ = (1 : ℝ)) → (∃ t, ψ t ≠ (1 : ℂ)) →
      ∃ n : ℤ, ∀ t : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v,
        (∀ s ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v,
          ψ (t * s) = (1 : ℂ)) ↔
        (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v →
          WithZero (Multiplicative ℤ)) t ≤ WithZero.exp n := by
  intro F _ _ v ψ hc _ hne
  exact exists_conductor ψ hc hne

end GlobalTheory.ConductorAdicCompletion
