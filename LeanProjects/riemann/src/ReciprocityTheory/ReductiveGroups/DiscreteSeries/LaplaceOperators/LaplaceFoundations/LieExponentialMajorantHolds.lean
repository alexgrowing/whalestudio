import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqZeroOfInPOfNoncompactRankZero

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant

variable {n : ℕ}

theorem re_trace_conj_diag {V : Matrix (Fin n) (Fin n) ℂ} (hV1 : star V * V = 1) (d : Fin n → ℝ) :
    (trace (V * diagonal (fun i => (d i : ℂ)) * star V)).re = ∑ i, d i := by
  rw [trace_conj hV1, trace_diagonal, Complex.re_sum]; simp

theorem diag_mul' (a b : Fin n → ℝ) :
    diagonal (fun i => (a i : ℂ)) * diagonal (fun i => (b i : ℂ)) =
      diagonal (fun i => ((a i * b i : ℝ) : ℂ)) := by
  rw [diagonal_mul_diagonal]; congr 1; funext i; push_cast; rfl

theorem diag_herm (a : Fin n → ℝ) :
    (diagonal (fun i => (a i : ℂ)))ᴴ = diagonal (fun i => (a i : ℂ)) := by
  rw [diagonal_conjTranspose]; congr 1; funext i; simp

theorem conj_herm (V : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ) :
    (V * diagonal (fun i => (a i : ℂ)) * star V)ᴴ = V * diagonal (fun i => (a i : ℂ)) * star V := by
  rw [conjTranspose_mul, conjTranspose_mul, diag_herm, star_eq_conjTranspose,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

theorem sum_bound (l : Fin n → ℝ) :
    ∑ i, (Real.exp (2 * l i) + Real.exp (-(2 * l i)) - 2) ≤
      4 * (∑ i, l i ^ 2) * Real.exp (2 * Real.sqrt (∑ i, l i ^ 2)) := by
  have hab : ∀ i, |l i| ≤ Real.sqrt (∑ j, l j ^ 2) := by
    intro i
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (l j)) (Finset.mem_univ i))
  calc ∑ i, (Real.exp (2 * l i) + Real.exp (-(2 * l i)) - 2)
      ≤ ∑ i, 4 * l i ^ 2 * Real.exp (2 * Real.sqrt (∑ j, l j ^ 2)) := by
        refine Finset.sum_le_sum fun i _ => (phi_le (l i)).trans ?_
        have := Real.exp_le_exp.mpr (show 2 * |l i| ≤ 2 * Real.sqrt (∑ j, l j ^ 2) by
          linarith [hab i])
        have h0 : 0 ≤ 4 * l i ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left this h0
    _ = 4 * (∑ i, l i ^ 2) * Real.exp (2 * Real.sqrt (∑ i, l i ^ 2)) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem hs_polar {g h κ V : Matrix (Fin n) (Fin n) ℂ} {l : Fin n → ℝ}
    (hV1 : star V * V = 1) (hk : star κ * κ = 1)
    (hgE : g = κ * (V * diagonal (fun i => (Real.exp (l i) : ℂ)) * star V))
    (hhg : h * g = 1) (htg : trace g = (n : ℂ)) (hth : trace h = (n : ℂ)) :
    S7.hs (g - 1) ≤ ∑ i, (Real.exp (2 * l i) + Real.exp (-(2 * l i)) - 2) := by
  set E := diagonal (fun i => (Real.exp (l i) : ℂ)) with hE
  have hgg : gᴴ * g = V * diagonal (fun i => ((Real.exp (l i) * Real.exp (l i) : ℝ) : ℂ)) * star V := by
    have e1 : gᴴ = V * E * star V * κᴴ := by
      rw [hgE, conjTranspose_mul, conj_herm]
    have hk' : κᴴ * κ = 1 := hk
    calc gᴴ * g = V * E * star V * (κᴴ * κ) * (V * E * star V) := by
          rw [e1, hgE]; simp only [Matrix.mul_assoc]
      _ = V * E * (star V * V) * E * star V := by
          rw [hk', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = V * (E * E) * star V := by rw [hV1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hE, diag_mul']
  set M := V * diagonal (fun i => ((Real.exp (-l i) * Real.exp (-l i) : ℝ) : ℂ)) * star V with hM
  have hgM : gᴴ * g * M = 1 := by
    have hdd : diagonal (fun i => ((Real.exp (l i) * Real.exp (l i) : ℝ) : ℂ)) *
        diagonal (fun i => ((Real.exp (-l i) * Real.exp (-l i) : ℝ) : ℂ)) = 1 := by
      rw [diag_mul', ← diagonal_one]; congr 1; funext i
      have : Real.exp (l i) * Real.exp (l i) * (Real.exp (-l i) * Real.exp (-l i)) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf; simp
      rw [this]; simp
    rw [hgg, hM]
    calc V * diagonal (fun i => ((Real.exp (l i) * Real.exp (l i) : ℝ) : ℂ)) * star V *
          (V * diagonal (fun i => ((Real.exp (-l i) * Real.exp (-l i) : ℝ) : ℂ)) * star V)
        = V * diagonal (fun i => ((Real.exp (l i) * Real.exp (l i) : ℝ) : ℂ)) * (star V * V) *
          diagonal (fun i => ((Real.exp (-l i) * Real.exp (-l i) : ℝ) : ℂ)) * star V := by
          simp only [Matrix.mul_assoc]
      _ = V * star V := by rw [hV1, Matrix.mul_one, Matrix.mul_assoc V, hdd, Matrix.mul_one]
      _ = 1 := mul_eq_one_comm.mp hV1
  have hgh : g * h = 1 := mul_eq_one_comm.mp hhg
  have hhh : h * hᴴ = M := by
    have h1 : gᴴ * g * (h * hᴴ) = 1 := by
      calc gᴴ * g * (h * hᴴ) = gᴴ * (g * h) * hᴴ := by simp only [Matrix.mul_assoc]
        _ = (h * g)ᴴ := by rw [hgh, Matrix.mul_one, conjTranspose_mul]
        _ = 1 := by rw [hhg, conjTranspose_one]
    have h2 : M * (gᴴ * g) = 1 := mul_eq_one_comm.mp hgM
    calc h * hᴴ = M * (gᴴ * g) * (h * hᴴ) := by rw [h2, Matrix.one_mul]
      _ = M := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hA := hs_sub_one g htg
  have hB := hs_sub_one h hth
  rw [hgg, re_trace_conj_diag hV1] at hA
  rw [trace_mul_comm, hhh, hM, re_trace_conj_diag hV1] at hB
  have hB0 : 0 ≤ S7.hs (h - 1) := by
    unfold S7.hs; positivity
  have hn : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
  have e2 : ∀ i, Real.exp (2 * l i) = Real.exp (l i) * Real.exp (l i) := fun i => by
    rw [← Real.exp_add]; ring_nf
  have e3 : ∀ i, Real.exp (-(2 * l i)) = Real.exp (-l i) * Real.exp (-l i) := fun i => by
    rw [← Real.exp_add]; ring_nf
  simp only [e2, e3]
  have : ∑ i, (Real.exp (l i) * Real.exp (l i) + Real.exp (-l i) * Real.exp (-l i) - 2) =
      (∑ i, Real.exp (l i) * Real.exp (l i) - n) + (∑ i, Real.exp (-l i) * Real.exp (-l i) - n) := by
    rw [hn, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  linarith

open ReciprocityTheory.ChartRestriction.DS

theorem neg_mem_lie {k r : ℕ} {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) :
    -Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r) := by
  intro t
  have := hY (-t)
  rw [Complex.ofReal_neg, neg_smul] at this
  rwa [smul_neg]

theorem hs_X_eq {n : ℕ} {X V : Matrix (Fin n) (Fin n) ℂ} {l : Fin n → ℝ} (hXh : X.IsHermitian)
    (hV1 : star V * V = 1) (hXV : X = V * diagonal (fun i => (l i : ℂ)) * star V) :
    S7.hs X = ∑ i, l i ^ 2 := by
  rw [hs_eq_re_trace, hXh.eq, hXV]
  have : V * diagonal (fun i => (l i : ℂ)) * star V * (V * diagonal (fun i => (l i : ℂ)) * star V) =
      V * diagonal (fun i => ((l i * l i : ℝ) : ℂ)) * star V := by
    calc _ = V * diagonal (fun i => (l i : ℂ)) * (star V * V) * diagonal (fun i => (l i : ℂ)) *
          star V := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV1, Matrix.mul_one, Matrix.mul_assoc V, diag_mul']
  rw [this, re_trace_conj_diag hV1]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem polar_a {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hPP : P⁻¹ * P = 1)
    (hPP' : P * P⁻¹ = 1) {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r))
    (κ : S7.KG ε) {X : Mat k r} (hX : inP ε X)
    (heq : P * NormedSpace.exp Y * P⁻¹ = S7.toMK κ * NormedSpace.exp X) :
    S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1) ≤
      4 * S7.hs X * Real.exp (2 * Real.sqrt (S7.hs X)) := by
  have htg : trace (P * NormedSpace.exp Y * P⁻¹) = ((2 * r + k + 1 : ℕ) : ℂ) := by
    rw [trace_conj hPP]; exact trace_exp_lie hY
  have hth : trace (P * NormedSpace.exp (-Y) * P⁻¹) = ((2 * r + k + 1 : ℕ) : ℂ) := by
    rw [trace_conj hPP]; exact trace_exp_lie (neg_mem_lie hY)
  have hhg : P * NormedSpace.exp (-Y) * P⁻¹ * (P * NormedSpace.exp Y * P⁻¹) = 1 := by
    have hx : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [Matrix.exp_neg]
      exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp Y))
    calc P * NormedSpace.exp (-Y) * P⁻¹ * (P * NormedSpace.exp Y * P⁻¹)
        = P * (NormedSpace.exp (-Y) * (P⁻¹ * P) * NormedSpace.exp Y) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Matrix.mul_one, hx, Matrix.mul_one, hPP']
  have hk : star (S7.toMK κ) * S7.toMK κ = 1 :=
    Unitary.star_mul_self_of_mem (show S7.toMK κ ∈ Kset ε from κ.2).1
  have hXh := herm_of_inP hX
  obtain ⟨V, l, hV1, _, hXV, hEV⟩ := herm_decomp hXh
  have hgE : P * NormedSpace.exp Y * P⁻¹ =
      S7.toMK κ * (V * diagonal (fun i => (Real.exp (l i) : ℂ)) * star V) := by
    rw [heq, hEV]
  have ha := hs_polar hV1 hk hgE hhg htg hth
  rw [hs_X_eq hXh hV1 hXV]
  exact ha.trans (sum_bound l)

theorem growth_a {k r : ℕ} {P : Mat k r} (hPP : P⁻¹ * P = 1) {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    {Y : Mat k r}
    (hgr : Real.sqrt (S7.hs Y) ≤ C * Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) *
      (1 + Real.sqrt (S7.hs (NormedSpace.exp Y - 1))) ^ m) :
    S7.hs Y ≤ (C * (max (Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P)) 1) ^ (m + 1)) ^ 2 *
      S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1) *
      (1 + Real.sqrt (S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1))) ^ (2 * m) := by
  obtain ⟨K1, hK1⟩ : ∃ K1, K1 = max (Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P)) 1 := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a, a = S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1) := ⟨_, rfl⟩
  rw [← hK1, ← had]
  have hK11 : 1 ≤ K1 := hK1 ▸ le_max_right _ _
  have hKK : Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P) ≤ K1 := hK1 ▸ le_max_left _ _
  have ha0 : 0 ≤ a := by rw [had]; unfold S7.hs; positivity
  have hexp : NormedSpace.exp Y - 1 = P⁻¹ * (P * NormedSpace.exp Y * P⁻¹ - 1) * P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hb : Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) ≤ K1 * Real.sqrt a := by
    rw [hexp]
    calc Real.sqrt (S7.hs (P⁻¹ * (P * NormedSpace.exp Y * P⁻¹ - 1) * P))
        ≤ Real.sqrt (S7.hs (P⁻¹ * (P * NormedSpace.exp Y * P⁻¹ - 1))) * Real.sqrt (S7.hs P) :=
          sqrt_hs_mul _ _
      _ ≤ Real.sqrt (S7.hs P⁻¹) * Real.sqrt a * Real.sqrt (S7.hs P) := by
          rw [had]; exact mul_le_mul_of_nonneg_right (sqrt_hs_mul _ _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P) * Real.sqrt a := by ring
      _ ≤ K1 * Real.sqrt a := mul_le_mul_of_nonneg_right hKK (Real.sqrt_nonneg _)
  have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hb0 : 0 ≤ Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) := Real.sqrt_nonneg _
  have hYb : Real.sqrt (S7.hs Y) ≤ C * K1 ^ (m + 1) * Real.sqrt a * (1 + Real.sqrt a) ^ m := by
    calc Real.sqrt (S7.hs Y)
        ≤ C * Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) *
          (1 + Real.sqrt (S7.hs (NormedSpace.exp Y - 1))) ^ m := hgr
      _ ≤ C * (K1 * Real.sqrt a) * (K1 * (1 + Real.sqrt a)) ^ m := by
          gcongr
          nlinarith
      _ = C * K1 ^ (m + 1) * Real.sqrt a * (1 + Real.sqrt a) ^ m := by rw [mul_pow, pow_succ]; ring
  have hY0 : 0 ≤ S7.hs Y := by unfold S7.hs; positivity
  rw [← Real.sq_sqrt hY0]
  calc Real.sqrt (S7.hs Y) ^ 2 ≤ (C * K1 ^ (m + 1) * Real.sqrt a * (1 + Real.sqrt a) ^ m) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hYb 2
    _ = (C * K1 ^ (m + 1)) ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt ha0, ← pow_mul, mul_comm m 2, mul_pow]

theorem final_ineq {A q s L : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (hs : 0 ≤ s) (hL : L ≤ A * min s (Real.sqrt s))
    (hq0 : q = 0 → s = 0) :
    1 / ((A + 1) * (1 + q)) * L ≤ min s (Real.sqrt s / q) := by
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = min s (Real.sqrt s) := ⟨_, rfl⟩
  rw [← hμ] at hL
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact le_min hs (Real.sqrt_nonneg _)
  have hA1 : 0 < A + 1 := by linarith
  have h1q : 0 < 1 + q := by linarith
  have hc : 1 / ((A + 1) * (1 + q)) * L ≤ μ / (1 + q) := by
    have hc0 : 0 ≤ 1 / ((A + 1) * (1 + q)) := by positivity
    calc 1 / ((A + 1) * (1 + q)) * L
        ≤ 1 / ((A + 1) * (1 + q)) * (A * μ) := mul_le_mul_of_nonneg_left hL hc0
      _ = A / (A + 1) * (μ / (1 + q)) := by field_simp
      _ ≤ 1 * (μ / (1 + q)) :=
          mul_le_mul_of_nonneg_right ((div_le_one hA1).mpr (by linarith)) (div_nonneg hμ0 h1q.le)
      _ = μ / (1 + q) := one_mul _
  have hμs : μ / (1 + q) ≤ s := (div_le_self hμ0 (by linarith)).trans (hμ ▸ min_le_left _ _)
  refine le_min (hc.trans hμs) ?_
  rcases eq_or_lt_of_le hq with h0 | h0
  · have hs0 : s = 0 := hq0 h0.symm
    have : μ = 0 := by rw [hμ, hs0]; simp
    rw [this] at hc
    rw [hs0]
    simpa using hc
  · calc 1 / ((A + 1) * (1 + q)) * L ≤ μ / (1 + q) := hc
      _ ≤ Real.sqrt s / (1 + q) := div_le_div_of_nonneg_right (hμ ▸ min_le_right _ _) h1q.le
      _ ≤ Real.sqrt s / q := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) h0 (by linarith)

theorem lieExponentialMajorant_holds : CayleyMajorantBound := by
  intro k r ε P hP
  obtain ⟨C, m, hC, hgr⟩ := (b4 k r).2.2.2.2
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  obtain ⟨A, hA, hlog⟩ :=
    log_bound (C * (max (Real.sqrt (S7.hs P⁻¹) * Real.sqrt (S7.hs P)) 1) ^ (m + 1)) m
  have hq : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  refine ⟨1 / ((A + 1) * (1 + Real.sqrt (2 * (S7.q0 ε : ℝ)))), by positivity,
    fun Y hY κ X hX heq => ?_⟩
  have hs0 : 0 ≤ S7.hs X := by unfold S7.hs; positivity
  have ha0 : 0 ≤ S7.hs (P * NormedSpace.exp Y * P⁻¹ - 1) := by unfold S7.hs; positivity
  have hY0 : 0 ≤ S7.hs Y := by unfold S7.hs; positivity
  have hL := hlog _ _ _ hs0 ha0 hY0 (polar_a hPP hPP' hY κ hX heq) (growth_a hPP hC (hgr Y hY))
  refine final_ineq hA hq hs0 hL fun h0 => ?_
  have hq0 : S7.q0 ε = 0 := by
    have h2 : (2 * (S7.q0 ε : ℝ)) = 0 := by
      have := Real.sqrt_eq_zero'.mp h0
      have h3 : (0 : ℝ) ≤ 2 * (S7.q0 ε : ℝ) := by positivity
      linarith
    exact_mod_cast (by linarith : (S7.q0 ε : ℝ) = 0)
  rw [eq_zero_of_noncompactPart_of_noncompactRank_zero hX hq0]
  simp [S7.hs]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant
