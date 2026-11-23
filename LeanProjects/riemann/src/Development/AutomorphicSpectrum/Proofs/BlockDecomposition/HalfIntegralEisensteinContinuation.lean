import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open Ad3 Ad3.S Filter Topology

namespace GlobalTheory.CompanionTheory.HalfInt

lemma norm_ee_mul (n : ℤ) (x : ℝ) : ‖ee ((n : ℂ) * (x : ℂ))‖ = 1 := by
  have : ee ((n : ℂ) * (x : ℂ)) = Complex.exp (((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I) := by
    unfold ee; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma rpow_le_add {e : ℝ} {A : ℕ} (h : |e| ≤ A) {y : ℝ} (hy : 0 < y) :
    y ^ e ≤ y ^ A + y⁻¹ ^ A := by
  rcases le_total 1 y with h1 | h1
  · have h2 : y ^ e ≤ y ^ (A : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 ((le_abs_self e).trans h)
    rw [Real.rpow_natCast] at h2
    have h3 := pow_nonneg (inv_pos.2 hy).le A
    linarith
  · have hi : 1 ≤ y⁻¹ := (one_le_inv₀ hy).2 h1
    have h2 : y⁻¹ ^ (-e) ≤ y⁻¹ ^ (A : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hi ((neg_le_abs e).trans h)
    rw [Real.rpow_natCast, Real.inv_rpow hy.le, Real.rpow_neg hy.le, inv_inv] at h2
    have h3 := pow_nonneg hy.le A
    linarith

lemma add_pow_le {A A' : ℕ} (h : A ≤ A') {y : ℝ} (hy : 0 < y) :
    y ^ A + y⁻¹ ^ A ≤ 2 * (y ^ A' + y⁻¹ ^ A') := by
  have hc : |(A : ℝ)| ≤ A' := by
    rw [abs_of_nonneg (Nat.cast_nonneg A)]; exact_mod_cast h
  have h1 := rpow_le_add hc hy
  have h2 := rpow_le_add (e := -(A : ℝ)) (by rwa [abs_neg]) hy
  rw [Real.rpow_natCast] at h1
  rw [Real.rpow_neg hy.le, Real.rpow_natCast, ← inv_pow] at h2
  linarith

lemma poly_le_exp (p : ℕ) (b : ℝ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, |s.re| ≤ b →
    (1 + ‖s‖) ^ p ≤ D * Real.exp (p * s.im ^ 2) := by
  refine ⟨((1 + |b|) * Real.exp 1) ^ p, by positivity, fun s hs => ?_⟩
  have h1 : 1 + ‖s‖ ≤ (1 + |b|) * Real.exp 1 * Real.exp (s.im ^ 2) := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    have ht : 1 + |s.im| ≤ Real.exp 1 * Real.exp (s.im ^ 2) := by
      rw [← Real.exp_add]
      have h3 : |s.im| ≤ 1 + s.im ^ 2 := by
        nlinarith [abs_nonneg s.im, sq_abs s.im, sq_nonneg (|s.im| - 1)]
      have h2 := Real.add_one_le_exp (1 + s.im ^ 2)
      nlinarith [sq_nonneg s.im]
    have hb : |s.re| ≤ |b| := hs.trans (le_abs_self b)
    calc 1 + ‖s‖ ≤ 1 + |b| + |s.im| := by linarith
      _ ≤ (1 + |b|) * (1 + |s.im|) := by nlinarith [abs_nonneg b, abs_nonneg s.im]
      _ ≤ (1 + |b|) * (Real.exp 1 * Real.exp (s.im ^ 2)) := by gcongr
      _ = _ := by ring
  calc (1 + ‖s‖) ^ p ≤ ((1 + |b|) * Real.exp 1 * Real.exp (s.im ^ 2)) ^ p := by gcongr
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]

theorem assemble (Q : ℂ → ℂ) (Tm : ℤ → ℂ → ℂ → ℂ)
    (hQd : DifferentiableOn ℂ Q (HP (1 / 4)))
    (hQb : ∀ b : ℝ, ∃ C : ℝ, ∀ s : ℂ, 1 / 4 < s.re → s.re ≤ b →
      ‖Q s‖ ≤ C * Real.exp (C * s.im ^ 2))
    (hd : ∀ (n : ℤ) (v : ℂ), 0 < v.im → DifferentiableOn ℂ (fun s => Tm n s v) (HP (1 / 4)))
    (hm : ∀ (n : ℤ), ∀ s ∈ HP (1 / 4), Measurable (Tm n s))
    (h0 : ∀ (n : ℤ) (s v : ℂ), v.im ≤ 0 → Tm n s v = 0)
    (hb : ∀ b : ℝ, ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ (n : ℤ) (s v : ℂ), 1 / 4 < s.re → s.re ≤ b →
      0 < v.im → ‖Tm n s v‖ ≤
        K * Real.exp (K * s.im ^ 2) * (v.im ^ A + v.im⁻¹ ^ A) * (1 / (n : ℝ) ^ 2)) :
    ∃ Es : ℂ → ℂ → ℂ,
      (∀ s v : ℂ, 0 < v.im → Es s v = Q s * (v.im : ℂ) ^ (1 / 2 - s) + ∑' n : ℤ, Tm n s v) ∧
      (∀ s v : ℂ, 1 / 4 < s.re → Summable fun n : ℤ => Tm n s v) ∧
      (∀ v : ℂ, 0 < v.im → DifferentiableOn ℂ (fun s => Es s v) (HP (1 / 4))) ∧
      (∀ s ∈ HP (1 / 4), Measurable (Es s)) ∧
      ∀ b : ℝ, ∃ (C : ℝ) (A : ℕ), ∀ s v : ℂ, 1 / 4 < s.re → s.re ≤ b → 0 < v.im →
        ‖Es s v‖ ≤ C * Real.exp (C * s.im ^ 2) * (v.im ^ A + v.im⁻¹ ^ A) := by
  have hS : Summable fun n : ℤ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_int_pow.2 (by norm_num)
  have hsum : ∀ s v : ℂ, 1 / 4 < s.re → Summable fun n : ℤ => Tm n s v := by
    intro s v hs
    rcases le_or_gt v.im 0 with hv | hv
    · simp only [h0 _ s v hv]; exact summable_zero
    · obtain ⟨K, A, -, hK⟩ := hb s.re
      exact Summable.of_norm_bounded (hS.mul_left _) fun n => hK n s v hs le_rfl hv
  refine ⟨fun s v => if 0 < v.im then Q s * (v.im : ℂ) ^ (1 / 2 - s) + ∑' n : ℤ, Tm n s v else 0,
    fun s v hv => if_pos hv, hsum, ?_, ?_, ?_⟩
  · intro v hv
    simp only [if_pos hv]
    have hy : (v.im : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    refine DifferentiableOn.add (hQd.mul ?_) ?_
    · exact DifferentiableOn.const_cpow ((differentiableOn_const _).sub differentiableOn_id) (Or.inl hy)
    · intro s₀ hs₀
      set R : ℝ := |s₀.re| + |s₀.im| + 1 with hR
      set U : Set ℂ := {s | 1 / 4 < s.re} ∩ ({s | s.re < R} ∩ ({s | s.im < R} ∩ {s | -R < s.im})) with hU
      have hUo : IsOpen U :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          ((isOpen_lt Complex.continuous_re continuous_const).inter
            ((isOpen_lt Complex.continuous_im continuous_const).inter
              (isOpen_lt continuous_const Complex.continuous_im)))
      have hsU : s₀ ∈ U := by
        refine ⟨hs₀, ?_, ?_, ?_⟩
        · show s₀.re < R
          have := le_abs_self s₀.re
          have := abs_nonneg s₀.im
          linarith
        · show s₀.im < R
          have := le_abs_self s₀.im
          have := abs_nonneg s₀.re
          linarith
        · show -R < s₀.im
          have := neg_abs_le s₀.im
          have := abs_nonneg s₀.re
          linarith
      obtain ⟨K, A, hK0, hK⟩ := hb R
      have hdU : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℤ, Tm n w v) U := by
        refine Complex.differentiableOn_tsum_of_summable_norm
          (u := fun n : ℤ => K * Real.exp (K * R ^ 2) * (v.im ^ A + v.im⁻¹ ^ A) * (1 / (n : ℝ) ^ 2))
          (hS.mul_left _) (fun n => (hd n v hv).mono fun s hs => hs.1) hUo ?_
        intro n w hw
        refine (hK n w v hw.1 hw.2.1.le hv).trans ?_
        have hsq : w.im ^ 2 ≤ R ^ 2 := sq_le_sq' hw.2.2.2.le hw.2.2.1.le
        have hyn : 0 ≤ v.im ^ A + v.im⁻¹ ^ A := by positivity
        gcongr
      exact (hdU.differentiableAt (hUo.mem_nhds hsU)).differentiableWithinAt
  · intro s hs
    refine Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) ?_ measurable_const
    refine Measurable.add ?_ ?_
    · exact measurable_const.mul ((Complex.measurable_ofReal.comp Complex.measurable_im).pow_const _)
    · refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℤ))
        (f := fun (t : Finset ℤ) v => ∑ n ∈ t, Tm n s v) (fun t => ?_) ?_
      · exact Finset.measurable_fun_sum t fun n _ => hm n s hs
      · exact tendsto_pi_nhds.2 fun v => (hsum s v hs).hasSum
  · intro b
    obtain ⟨C, hC⟩ := hQb b
    obtain ⟨K, A, hK0, hK⟩ := hb b
    set Z : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2 with hZ
    have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
    set A' : ℕ := max A ⌈1 / 2 + |b|⌉₊ with hA'
    set K' : ℝ := |C| + 2 * K * Z + K with hK'
    have hK'0 : 0 ≤ K' := by positivity
    refine ⟨K', A', fun s v hs hsb hv => ?_⟩
    have hW0 : 0 ≤ v.im ^ A' + v.im⁻¹ ^ A' := by positivity
    have hW1 : 0 ≤ v.im ^ A + v.im⁻¹ ^ A := by positivity
    have hexp : 0 < Real.exp (K' * s.im ^ 2) := Real.exp_pos _
    have hsq := sq_nonneg s.im
    have hT : ‖∑' n : ℤ, Tm n s v‖ ≤ K * Real.exp (K' * s.im ^ 2) * (2 * (v.im ^ A' + v.im⁻¹ ^ A')) * Z := by
      have hHS : HasSum (fun n : ℤ => K * Real.exp (K * s.im ^ 2) * (v.im ^ A + v.im⁻¹ ^ A) * (1 / (n : ℝ) ^ 2))
          (K * Real.exp (K * s.im ^ 2) * (v.im ^ A + v.im⁻¹ ^ A) * Z) := hS.hasSum.mul_left _
      refine (tsum_of_norm_bounded hHS fun n => hK n s v hs hsb hv).trans ?_
      have h1 : K ≤ K' := by rw [hK']; have := abs_nonneg C; nlinarith [abs_nonneg C, mul_nonneg hK0 hZ0]
      have h2 := add_pow_le (le_max_left A _ : A ≤ A') hv
      gcongr
    have hQ' : ‖Q s * (v.im : ℂ) ^ (1 / 2 - s)‖ ≤ |C| * Real.exp (K' * s.im ^ 2) * (v.im ^ A' + v.im⁻¹ ^ A') := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv]
      have hre : (1 / 2 - s).re = 1 / 2 - s.re := by simp
      rw [hre]
      have hab : |1 / 2 - s.re| ≤ (A' : ℝ) := by
        have h3 : (1 / 2 + |b| : ℝ) ≤ (A' : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast le_max_right A _)
        have h4 := le_abs_self b
        rw [abs_le]; constructor <;> linarith
      have h5 := rpow_le_add hab hv
      have h6 : ‖Q s‖ ≤ |C| * Real.exp (K' * s.im ^ 2) := by
        refine (hC s hs hsb).trans ?_
        have h7 : C ≤ |C| := le_abs_self C
        have h8 : |C| ≤ K' := by rw [hK']; nlinarith [abs_nonneg C, mul_nonneg hK0 hZ0]
        calc C * Real.exp (C * s.im ^ 2) ≤ |C| * Real.exp (C * s.im ^ 2) := by gcongr
          _ ≤ |C| * Real.exp (K' * s.im ^ 2) := by
              have : C ≤ K' := h7.trans h8
              gcongr
      exact mul_le_mul h6 h5 (Real.rpow_nonneg hv.le _) (by positivity)
    simp only [if_pos hv]
    calc _ ≤ ‖Q s * (v.im : ℂ) ^ (1 / 2 - s)‖ + ‖∑' n : ℤ, Tm n s v‖ := norm_add_le _ _
      _ ≤ |C| * Real.exp (K' * s.im ^ 2) * (v.im ^ A' + v.im⁻¹ ^ A') +
          K * Real.exp (K' * s.im ^ 2) * (2 * (v.im ^ A' + v.im⁻¹ ^ A')) * Z := add_le_add hQ' hT
      _ = (|C| + 2 * K * Z) * Real.exp (K' * s.im ^ 2) * (v.im ^ A' + v.im⁻¹ ^ A') := by ring
      _ ≤ K' * Real.exp (K' * s.im ^ 2) * (v.im ^ A' + v.im⁻¹ ^ A') := by
          have : |C| + 2 * K * Z ≤ K' := by rw [hK']; linarith
          gcongr

theorem half_integral_eisenstein_continuation : A0 → A1 → W0 → W1 → W2 → P2 → E0 := by
  intro hA0 hA1 hW0 hW1 hW2 hP2 M k ν _ h2 c
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((ν : ℝ) + 1 - k) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ((k : ℝ) - ν) / 2 := ⟨_, rfl⟩
  have hab : a + b = 1 / 2 := by rw [ha, hb]; ring
  have hal : ∀ s : ℂ, al k ν s = s / 2 + (a : ℂ) := fun s => by
    unfold al; rw [ha]; push_cast; ring
  have hbe : ∀ s : ℂ, be k ν s = s / 2 + (b : ℂ) := fun s => by
    unfold be; rw [hb]; push_cast; ring
  have hal1 : ∀ s : ℂ, al k ν s + 1 = s / 2 + ((a + 1 : ℝ) : ℂ) := fun s => by
    rw [hal]; push_cast; ring
  obtain ⟨C0, A0f, hA0d, hA0id, hA0b⟩ := hA0 M h2 c
  obtain ⟨C1, B, h1⟩ := hA1 M h2 c
  choose! An hAd hAid hAb using h1
  obtain ⟨Ψ, hΨd, hΨm, hΨid, hΨb⟩ := hW2 (B + 2) a b
  obtain ⟨hΦd, -, hΦb⟩ := hW0 (a + 1) b
  have hBc : (((B + 2 : ℕ)) : ℝ) = (B : ℝ) + 2 := by push_cast; ring
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hsubΨ : HP (1 / 4) ⊆ HP (1 - a - b - ((B + 2 : ℕ) : ℝ)) := by
    intro s hs
    have hs' : 1 / 4 < s.re := hs
    show 1 - a - b - ((B + 2 : ℕ) : ℝ) < s.re
    rw [hBc]; linarith
  have hsubΦ : HP (1 / 4) ⊆ HP (1 - (a + 1) - b) := by
    intro s hs
    have hs' : 1 / 4 < s.re := hs
    show 1 - (a + 1) - b < s.re
    linarith

  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ → ℂ, ∀ s, Q s = A0f s * (2 * al k ν s * Phi (al k ν s + 1) (be k ν s) 0) :=
    ⟨_, fun _ => rfl⟩
  have hQd : DifferentiableOn ℂ Q (HP (1 / 4)) := by
    have e : Q = fun s => A0f s * (2 * (s / 2 + (a : ℂ)) *
        Phi (s / 2 + ((a + 1 : ℝ) : ℂ)) (s / 2 + (b : ℂ)) 0) :=
      funext fun s => by rw [hQ, hal1, hal, hbe]
    rw [e]
    refine hA0d.mul (DifferentiableOn.mul ?_ ((hΦd 0).mono hsubΦ))
    fun_prop
  have hQb : ∀ b' : ℝ, ∃ C : ℝ, ∀ s : ℂ, 1 / 4 < s.re → s.re ≤ b' →
      ‖Q s‖ ≤ C * Real.exp (C * s.im ^ 2) := by
    intro b'
    obtain ⟨C3, hC3⟩ := hΦb (1 / 2) b' (by norm_num)
    obtain ⟨D, hD0, hD⟩ := poly_le_exp 5 (|b'| + 1)
    refine ⟨|C0| * (1 + 2 * |a|) * |C3| * D + |C3| + 5, fun s hs hsb => ?_⟩
    have hsq := sq_nonneg s.im
    have hsabs : |s.re| ≤ |b'| + 1 := by
      rw [abs_of_pos (by linarith)]
      have := le_abs_self b'
      linarith
    have hP : (1 + ‖s‖) ^ 5 ≤ D * Real.exp (5 * s.im ^ 2) := by
      have := hD s hsabs
      push_cast at this
      exact this
    have n1 : ‖A0f s‖ ≤ |C0| * (1 + ‖s‖) ^ 4 := by
      refine (hA0b s hs).trans ?_
      have := le_abs_self C0
      gcongr
    have n2 : ‖2 * al k ν s‖ ≤ (1 + 2 * |a|) * (1 + ‖s‖) := by
      have e : 2 * al k ν s = s + 2 * (a : ℂ) := by rw [hal]; ring
      rw [e]
      have h3 : ‖2 * (a : ℂ)‖ = 2 * |a| := by simp
      have h4 := norm_add_le s (2 * (a : ℂ))
      rw [h3] at h4
      nlinarith [abs_nonneg a, norm_nonneg s]
    have n3 : ‖Phi (al k ν s + 1) (be k ν s) 0‖ ≤ |C3| * Real.exp (|C3| * s.im ^ 2) := by
      rw [hal1, hbe]
      refine (hC3 s 0 (by linarith) hsb).trans ?_
      have := le_abs_self C3
      gcongr
    rw [hQ]
    calc ‖A0f s * (2 * al k ν s * Phi (al k ν s + 1) (be k ν s) 0)‖
        = ‖A0f s‖ * (‖2 * al k ν s‖ * ‖Phi (al k ν s + 1) (be k ν s) 0‖) := by
          rw [norm_mul, norm_mul]
      _ ≤ (|C0| * (1 + ‖s‖) ^ 4) * (((1 + 2 * |a|) * (1 + ‖s‖)) *
          (|C3| * Real.exp (|C3| * s.im ^ 2))) := by gcongr
      _ = (|C0| * (1 + 2 * |a|) * |C3|) * (1 + ‖s‖) ^ 5 * Real.exp (|C3| * s.im ^ 2) := by ring
      _ ≤ (|C0| * (1 + 2 * |a|) * |C3|) * (D * Real.exp (5 * s.im ^ 2)) *
          Real.exp (|C3| * s.im ^ 2) := by gcongr
      _ = (|C0| * (1 + 2 * |a|) * |C3| * D) * Real.exp ((5 + |C3|) * s.im ^ 2) := by
          rw [add_mul, Real.exp_add]; ring
      _ ≤ _ := by
          have h5 : |C0| * (1 + 2 * |a|) * |C3| * D ≤ |C0| * (1 + 2 * |a|) * |C3| * D + |C3| + 5 := by
            have := abs_nonneg C3
            linarith
          have h6 : 5 + |C3| ≤ |C0| * (1 + 2 * |a|) * |C3| * D + |C3| + 5 := by
            have : 0 ≤ |C0| * (1 + 2 * |a|) * |C3| * D := by positivity
            linarith
          gcongr

  obtain ⟨Tm, hTm⟩ : ∃ Tm : ℤ → ℂ → ℂ → ℂ, ∀ n s v, Tm n s v = if n = 0 ∨ v.im ≤ 0 then 0 else
      An n s * (v.im : ℂ) ^ (1 / 2 - s) * Ψ s ((n : ℝ) * v.im) * ee ((n : ℂ) * (v.re : ℂ)) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hT1 : ∀ (n : ℤ) (s v : ℂ), n ≠ 0 → 0 < v.im → Tm n s v =
      An n s * (v.im : ℂ) ^ (1 / 2 - s) * Ψ s ((n : ℝ) * v.im) * ee ((n : ℂ) * (v.re : ℂ)) := by
    intro n s v hn hv
    rw [hTm, if_neg]
    push_neg
    exact ⟨hn, hv⟩
  have hT0 : ∀ (n : ℤ) (s v : ℂ), v.im ≤ 0 → Tm n s v = 0 := by
    intro n s v hv
    rw [hTm, if_pos (Or.inr hv)]
  have hTz : ∀ (s v : ℂ), Tm 0 s v = 0 := by
    intro s v
    rw [hTm, if_pos (Or.inl rfl)]
  have hTd : ∀ (n : ℤ) (v : ℂ), 0 < v.im → DifferentiableOn ℂ (fun s => Tm n s v) (HP (1 / 4)) := by
    intro n v hv
    by_cases hn : n = 0
    · subst hn
      simp only [hTz]
      exact differentiableOn_const _
    · have e : (fun s => Tm n s v) = fun s => An n s * (v.im : ℂ) ^ (1 / 2 - s) *
          Ψ s ((n : ℝ) * v.im) * ee ((n : ℂ) * (v.re : ℂ)) := funext fun s => hT1 n s v hn hv
      have hy : (v.im : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
      rw [e]
      refine DifferentiableOn.mul (DifferentiableOn.mul (DifferentiableOn.mul (hAd n hn) ?_)
        ((hΨd _).mono hsubΨ)) (differentiableOn_const _)
      exact DifferentiableOn.const_cpow ((differentiableOn_const _).sub differentiableOn_id) (Or.inl hy)
  have hTme : ∀ (n : ℤ), ∀ s ∈ HP (1 / 4), Measurable (Tm n s) := by
    intro n s hs
    by_cases hn : n = 0
    · subst hn
      have e : Tm 0 s = fun _ => 0 := funext fun v => hTz s v
      rw [e]
      exact measurable_const
    · have e : Tm n s = fun v => if v.im ≤ 0 then 0 else
          An n s * (v.im : ℂ) ^ (1 / 2 - s) * Ψ s ((n : ℝ) * v.im) * ee ((n : ℂ) * (v.re : ℂ)) :=
        funext fun v => by rw [hTm]; simp [hn]
      rw [e]
      refine Measurable.ite (measurableSet_le Complex.measurable_im measurable_const)
        measurable_const ?_
      refine Measurable.mul (Measurable.mul (Measurable.mul measurable_const ?_) ?_) ?_
      · exact (Complex.measurable_ofReal.comp Complex.measurable_im).pow_const _
      · exact (hΨm s (hsubΨ hs)).comp (measurable_const.mul Complex.measurable_im)
      · unfold ee
        exact Complex.measurable_exp.comp (measurable_const.mul (measurable_const.mul
          (Complex.measurable_ofReal.comp Complex.measurable_re)))
  have hTb : ∀ b' : ℝ, ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ (n : ℤ) (s v : ℂ), 1 / 4 < s.re → s.re ≤ b' →
      0 < v.im → ‖Tm n s v‖ ≤
        K * Real.exp (K * s.im ^ 2) * (v.im ^ A + v.im⁻¹ ^ A) * (1 / (n : ℝ) ^ 2) := by
    intro b'
    obtain ⟨C2, hC2⟩ := hΨb 1 b' one_pos
    obtain ⟨D, hD0, hD⟩ := poly_le_exp 4 (|b'| + 1)
    refine ⟨|C1| * |C2| * D + |C2| + 4, ⌈1 / 2 + |b'| + ((B + 2 : ℕ) : ℝ)⌉₊, by positivity,
      fun n s v hs hsb hv => ?_⟩
    by_cases hn : n = 0
    · subst hn
      rw [hTz]
      simp
    have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    have hN : 0 < |(n : ℝ)| := abs_pos.2 hnR
    have hξ : (n : ℝ) * v.im ≠ 0 := mul_ne_zero hnR hv.ne'
    have hsq := sq_nonneg s.im
    have hsabs : |s.re| ≤ |b'| + 1 := by
      rw [abs_of_pos (by linarith)]
      have := le_abs_self b'
      linarith
    have hP : (1 + ‖s‖) ^ 4 ≤ D * Real.exp (4 * s.im ^ 2) := by
      have := hD s hsabs
      push_cast at this
      exact this
    have n1 : ‖An n s‖ ≤ |C1| * |(n : ℝ)| ^ B * (1 + ‖s‖) ^ 4 := by
      refine (hAb n hn s hs).trans ?_
      have := le_abs_self C1
      gcongr
    have n2 : ‖Ψ s ((n : ℝ) * v.im)‖ ≤
        |C2| * Real.exp (|C2| * s.im ^ 2) / (|(n : ℝ)| * v.im) ^ (B + 2) := by
      refine (hC2 s _ hξ ?_ hsb).trans ?_
      · rw [hBc]; linarith
      · rw [abs_mul, abs_of_pos hv]
        have := le_abs_self C2
        gcongr
    have n3 : ‖(v.im : ℂ) ^ (1 / 2 - s)‖ = v.im ^ (1 / 2 - s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
      simp
    have hexpo : |1 / 2 - s.re - ((B + 2 : ℕ) : ℝ)| ≤
        ((⌈1 / 2 + |b'| + ((B + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
      refine le_trans ?_ (Nat.le_ceil _)
      have h4 := le_abs_self b'
      rw [hBc]
      rw [abs_le]; constructor <;> linarith
    have hW := rpow_le_add hexpo hv
    rw [Real.rpow_sub hv, Real.rpow_natCast] at hW
    obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = v.im ^ ⌈1 / 2 + |b'| + ((B + 2 : ℕ) : ℝ)⌉₊ +
      v.im⁻¹ ^ ⌈1 / 2 + |b'| + ((B + 2 : ℕ) : ℝ)⌉₊ := ⟨_, rfl⟩
    rw [← hWd] at hW ⊢
    have hW0 : 0 ≤ W := by rw [hWd]; positivity
    have hy0 : 0 ≤ v.im ^ (1 / 2 - s.re) := Real.rpow_nonneg hv.le _
    rw [hT1 n s v hn hv, norm_mul, norm_mul, norm_mul, norm_ee_mul, n3, mul_one]
    calc ‖An n s‖ * v.im ^ (1 / 2 - s.re) * ‖Ψ s ((n : ℝ) * v.im)‖
        ≤ (|C1| * |(n : ℝ)| ^ B * (1 + ‖s‖) ^ 4) * v.im ^ (1 / 2 - s.re) *
          (|C2| * Real.exp (|C2| * s.im ^ 2) / (|(n : ℝ)| * v.im) ^ (B + 2)) := by gcongr
      _ = (|C1| * |C2| * (1 + ‖s‖) ^ 4 * Real.exp (|C2| * s.im ^ 2)) *
          (v.im ^ (1 / 2 - s.re) / v.im ^ (B + 2)) * (1 / (n : ℝ) ^ 2) := by
          rw [← sq_abs (n : ℝ), mul_pow, pow_add |(n : ℝ)|]
          field_simp
      _ ≤ (|C1| * |C2| * (D * Real.exp (4 * s.im ^ 2)) * Real.exp (|C2| * s.im ^ 2)) * W *
          (1 / (n : ℝ) ^ 2) := by gcongr
      _ = (|C1| * |C2| * D) * Real.exp ((4 + |C2|) * s.im ^ 2) * W * (1 / (n : ℝ) ^ 2) := by
          rw [add_mul, Real.exp_add]; ring
      _ ≤ _ := by
          have h5 : |C1| * |C2| * D ≤ |C1| * |C2| * D + |C2| + 4 := by
            have := abs_nonneg C2
            linarith
          have h6 : 4 + |C2| ≤ |C1| * |C2| * D + |C2| + 4 := by
            have : 0 ≤ |C1| * |C2| * D := by positivity
            linarith
          gcongr
  obtain ⟨Es, hEs, hsum, hd, hm, hbd⟩ := assemble Q Tm hQd hQb hTd hTme hT0 hTb
  refine ⟨Es, hd, hm, ?_, hbd⟩
  intro s v hs hv
  have hs4 : 1 / 4 < s.re := by linarith
  have hsHP : s ∈ HP (1 - a - b) := by
    show 1 - a - b < s.re
    linarith
  have hαβ : al k ν s + be k ν s = s + 1 / 2 := by unfold al be; ring
  have hw := (hW1 (al k ν s) (be k ν s) (by rw [hαβ]; simp; linarith)).2
  rw [hαβ] at hw
  have hid := hA0id s hs
  rw [hEs s v hv, hP2 M k ν h2 c s v hs hv, ← tsum_mul_left]
  obtain ⟨g, hgd⟩ : ∃ g : ℤ → ℂ, ∀ n : ℤ, g n = (s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s) *
      (Dn c n s * (v.im : ℂ) ^ (1 / 2 - s) * Phi (al k ν s) (be k ν s) ((n : ℝ) * v.im) *
        ee ((n : ℂ) * (v.re : ℂ))) := ⟨_, fun _ => rfl⟩
  have hg : ∀ n : ℤ, n ≠ 0 → g n = Tm n s v := by
    intro n hn
    have hξ : (n : ℝ) * v.im ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hn) hv.ne'
    rw [hgd, hT1 n s v hn hv, hAid n hn s hs, hΨid s hsHP _ hξ, hal, hbe]
    ring
  have hg0 : g 0 = Q s * (v.im : ℂ) ^ (1 / 2 - s) := by
    have hee : ee 0 = 1 := by simp [ee]
    have z1 : (((0 : ℤ) : ℝ) * v.im) = 0 := by simp
    have z2 : (((0 : ℤ) : ℂ) * (v.re : ℂ)) = 0 := by simp
    rw [hgd, z1, z2, hee, hQ, mul_one, ← hw]
    have e : A0f s * ((s + 1 / 2 - 1) * Phi (al k ν s) (be k ν s) 0) * (v.im : ℂ) ^ (1 / 2 - s) =
        ((s - 1 / 2) * A0f s) * ((v.im : ℂ) ^ (1 / 2 - s) * Phi (al k ν s) (be k ν s) 0) := by ring
    rw [e, hid]
    ring
  have hgS : Summable g := by
    have e : g = fun n => Tm n s v + if n = 0 then g 0 else 0 := by
      funext n
      by_cases hn : n = 0
      · subst hn; simp [hTz]
      · simp [hn, hg n hn]
    rw [e]
    exact (hsum s v hs4).add (hasSum_ite_eq (0 : ℤ) (g 0)).summable
  have hgE : (fun n : ℤ => (s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s) *
      (Dn c n s * (v.im : ℂ) ^ (1 / 2 - s) * Phi (al k ν s) (be k ν s) ((n : ℝ) * v.im) *
        ee ((n : ℂ) * (v.re : ℂ)))) = g := funext fun n => (hgd n).symm
  rw [hgE, hgS.tsum_eq_add_tsum_ite 0, hg0]
  congr 1
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [hTz]
  · simp [hn, hg n hn]

end GlobalTheory.CompanionTheory.HalfInt
