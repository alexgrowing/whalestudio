import Formalism.HermitianCurvature.StatementE

namespace Formalism.FourierDecayAlt.P.Markov

open Polynomial Real Finset

theorem abs_eval_le_of_nodes (s : Finset ℕ) (v : ℕ → ℝ) (hvs : Set.InjOn v s) (r : ℝ[X])
    (hr : r.degree < #s) (K : ℝ)
    (hK : ∀ i ∈ s, |r.eval (v i)| ≤ K * |(derivative (Lagrange.nodal s v)).eval (v i)|)
    (y : ℝ) (hy : ∀ i ∈ s, v i < y) :
    |r.eval y| ≤ K * (derivative (Lagrange.nodal s v)).eval y := by
  have hne : ∀ i ∈ s, y ≠ v i := fun i hi => (hy i hi).ne'
  have hNpos : 0 < (Lagrange.nodal s v).eval y := by
    rw [Lagrange.eval_nodal]; exact Finset.prod_pos fun i hi => sub_pos.mpr (hy i hi)
  have hd : (derivative (Lagrange.nodal s v)).degree < #s := by
    have := degree_derivative_lt (Lagrange.nodal_ne_zero (s := s) (v := v))
    rwa [Lagrange.degree_nodal] at this
  have e1 : r.eval y = (Lagrange.nodal s v).eval y *
      ∑ i ∈ s, Lagrange.nodalWeight s v i * (y - v i)⁻¹ * r.eval (v i) := by
    conv_lhs => rw [Lagrange.eq_interpolate hvs hr]
    exact Lagrange.eval_interpolate_not_at_node _ hne
  have e2 : (derivative (Lagrange.nodal s v)).eval y = (Lagrange.nodal s v).eval y *
      ∑ i ∈ s, Lagrange.nodalWeight s v i * (y - v i)⁻¹ *
        (derivative (Lagrange.nodal s v)).eval (v i) := by
    conv_lhs => rw [Lagrange.eq_interpolate hvs hd]
    exact Lagrange.eval_interpolate_not_at_node _ hne
  have hw : ∀ i ∈ s, Lagrange.nodalWeight s v i *
      (derivative (Lagrange.nodal s v)).eval (v i) = 1 := by
    intro i hi
    have h0 := Lagrange.nodalWeight_ne_zero hvs hi
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi] at h0 ⊢
    exact inv_mul_cancel₀ (by simpa using h0)
  rw [e1, e2, abs_mul, abs_of_pos hNpos, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ hNpos.le
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hpos : 0 < (y - v i)⁻¹ := inv_pos.mpr (sub_pos.mpr (hy i hi))
  have h1 := hw i hi
  have h2 : |Lagrange.nodalWeight s v i| *
      |(derivative (Lagrange.nodal s v)).eval (v i)| = 1 := by
    rw [← abs_mul, h1, abs_one]
  rw [abs_mul, abs_mul, abs_of_pos hpos]
  calc |Lagrange.nodalWeight s v i| * (y - v i)⁻¹ * |r.eval (v i)|
      ≤ |Lagrange.nodalWeight s v i| * (y - v i)⁻¹ *
        (K * |(derivative (Lagrange.nodal s v)).eval (v i)|) := by
        exact mul_le_mul_of_nonneg_left (hK i hi) (mul_nonneg (abs_nonneg _) hpos.le)
    _ = K * (y - v i)⁻¹ * (|Lagrange.nodalWeight s v i| *
        |(derivative (Lagrange.nodal s v)).eval (v i)|) := by ring
    _ = K * ((y - v i)⁻¹ * (Lagrange.nodalWeight s v i *
        (derivative (Lagrange.nodal s v)).eval (v i))) := by rw [h1, h2]; ring
    _ = _ := by ring

noncomputable def th (n k : ℕ) : ℝ := (2 * k + 1) * π / (2 * n)

theorem injOn_cos_th (n : ℕ) : Set.InjOn (fun k => cos (th n k)) (Finset.range n : Finset ℕ) :=
  (Finset.range n).nodup_map_iff_injOn.mp (Chebyshev.roots_T_real_nodup n)

theorem T_eq_nodal (n : ℕ) (hn : n ≠ 0) :
    Chebyshev.T ℝ n =
      C ((2 : ℝ) ^ (n - 1)) * Lagrange.nodal (Finset.range n) (fun k => cos (th n k)) := by
  have h2 : ((2 : ℝ) ^ (n - 1)) ≠ 0 := by positivity
  apply eq_of_degree_le_of_eval_index_eq (Finset.range n) (injOn_cos_th n)
  · simp
  · rw [degree_C_mul h2, Lagrange.degree_nodal]; simp
  · rw [leadingCoeff_mul, leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff]; simp
  · intro i hi
    have h0 : eval (cos (th n i)) (Lagrange.nodal (Finset.range n) fun k => cos (th n k)) = 0 :=
      Lagrange.eval_nodal_at_node (v := fun k => cos (th n k)) hi
    rw [eval_mul, h0, mul_zero, Chebyshev.T_real_cos, cos_eq_zero_iff]
    refine ⟨i, ?_⟩
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [th]
    push_cast
    field_simp

theorem th_pos (n k : ℕ) (hn : n ≠ 0) : 0 < th n k := by
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold th; positivity

theorem th_lt_pi {n k : ℕ} (hk : k < n) : th n k < π := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  unfold th
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_pos]

theorem abs_U_mul_sin (n k : ℕ) (hn : n ≠ 0) :
    |(Chebyshev.U ℝ ((n : ℤ) - 1)).eval (cos (th n k))| * |sin (th n k)| = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← abs_mul, Chebyshev.U_real_cos]
  have : ((((n : ℤ) - 1 : ℤ) : ℝ) + 1) * th n k = k * π + π / 2 := by
    push_cast; simp only [th]; field_simp; ring
  rw [this, sin_add_pi_div_two, cos_nat_mul_pi]
  simp

theorem schur (n : ℕ) (hn : n ≠ 0) (r : ℝ[X]) (hr : r.degree < n) (c : ℝ)
    (hC : ∀ k < n, |sin (th n k) * r.eval (cos (th n k))| ≤ c)
    (y : ℝ) (hy : ∀ k < n, cos (th n k) < y) (hy1 : y ≤ 1) : |r.eval y| ≤ n * c := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc : 0 ≤ c := (abs_nonneg _).trans (hC 0 hn0)
  have hym : -1 ≤ y := (neg_one_le_cos _).trans (hy 0 hn0).le
  have hT' : derivative (Chebyshev.T ℝ n) = C ((2 : ℝ) ^ (n - 1)) *
      derivative (Lagrange.nodal (Finset.range n) (fun k => cos (th n k))) := by
    conv_lhs => rw [T_eq_nodal n hn, derivative_C_mul]
  have hTe : ∀ x : ℝ, (derivative (Chebyshev.T ℝ n)).eval x = (2 : ℝ) ^ (n - 1) *
      (derivative (Lagrange.nodal (Finset.range n) (fun k => cos (th n k)))).eval x := by
    intro x; rw [hT']; simp
  have hUe : ∀ x : ℝ, (derivative (Chebyshev.T ℝ n)).eval x =
      n * (Chebyshev.U ℝ ((n : ℤ) - 1)).eval x := by
    intro x; rw [Chebyshev.T_derivative_eq_U]; simp
  have key := abs_eval_le_of_nodes (Finset.range n) (fun k => cos (th n k)) (injOn_cos_th n) r
    (by simpa using hr) (c / n * 2 ^ (n - 1)) ?_ y (by simpa using hy)
  · have h2 : (derivative (Chebyshev.T ℝ n)).eval y ≤ (n : ℝ) ^ 2 := by
      have h3 := Chebyshev.abs_iterate_derivative_T_real_le n 1 (x := y) (abs_le.mpr ⟨hym, hy1⟩)
      simp only [Function.iterate_one, Chebyshev.derivative_T_eval_one] at h3
      exact (le_abs_self _).trans (by simpa using h3)
    calc |r.eval y| ≤ c / n * ((2 : ℝ) ^ (n - 1) *
          (derivative (Lagrange.nodal (Finset.range n) (fun k => cos (th n k)))).eval y) := by
          rw [← mul_assoc]; exact key
      _ = c / n * (derivative (Chebyshev.T ℝ n)).eval y := by rw [hTe]
      _ ≤ c / n * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = n * c := by field_simp
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have h1 := abs_U_mul_sin n k hn
    have h2 := hC k hk'
    rw [abs_mul] at h2
    have h3 : c / n * 2 ^ (n - 1) *
        |(derivative (Lagrange.nodal (Finset.range n) (fun k => cos (th n k)))).eval
          (cos (th n k))| = c * |(Chebyshev.U ℝ ((n : ℤ) - 1)).eval (cos (th n k))| := by
      have h4 := (hTe (cos (th n k))).symm.trans (hUe (cos (th n k)))
      have h5 := congrArg abs h4
      rw [abs_mul, abs_mul, abs_of_pos hn', abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n - 1))] at h5
      rw [mul_assoc, h5]; field_simp
    show |r.eval (cos (th n k))| ≤ _
    rw [h3]
    calc |r.eval (cos (th n k))|
        = (|sin (th n k)| * |r.eval (cos (th n k))|) *
          |(Chebyshev.U ℝ ((n : ℤ) - 1)).eval (cos (th n k))| := by
          rw [mul_right_comm, mul_comm |sin (th n k)|, h1, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)

noncomputable def rot (a b : ℝ) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 0)
  | m + 1 => (C a * X * (rot a b m).1 + C b * ((1 - X ^ 2) * (rot a b m).2),
              C b * (rot a b m).1 + C a * X * (rot a b m).2)

theorem rot_eval (a b : ℝ) (m : ℕ) (y z : ℝ) (h : y ^ 2 + z ^ 2 = 1) :
    (a * y + b * z) ^ m = (rot a b m).1.eval y + z * (rot a b m).2.eval y := by
  induction m with
  | zero => simp [rot]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [rot, eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_one, eval_pow]
    linear_combination (b * (rot a b m).2.eval y) * h

theorem rot_natDegree (a b : ℝ) (m : ℕ) :
    (rot a b m).1.natDegree ≤ m ∧ (rot a b (m + 1)).2.natDegree ≤ m ∧
      ((1 - X ^ 2) * (rot a b m).2).natDegree ≤ m + 1 := by
  induction m with
  | zero => simp [rot]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hA : (rot a b (m + 1)).1.natDegree ≤ m + 1 := by
      show (C a * X * (rot a b m).1 + C b * ((1 - X ^ 2) * (rot a b m).2)).natDegree ≤ m + 1
      refine natDegree_add_le_of_degree_le ?_ ((natDegree_C_mul_le _ _).trans h3)
      rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X]; omega
    refine ⟨hA, ?_, ?_⟩
    · show (C b * (rot a b (m + 1)).1 + C a * X * (rot a b (m + 1)).2).natDegree ≤ m + 1
      refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hA) ?_
      rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X]; omega
    · refine natDegree_mul_le.trans ?_
      have : ((1 : ℝ[X]) - X ^ 2).natDegree ≤ 2 := by compute_degree
      omega

theorem exists_rot (a b : ℝ) (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) :
    ∃ A B : ℝ[X], B.degree < n ∧ ∀ y z : ℝ, y ^ 2 + z ^ 2 = 1 →
      p.eval (a * y + b * z) = A.eval y + z * B.eval y := by
  refine ⟨∑ m ∈ Finset.range (n + 1), C (p.coeff m) * (rot a b m).1,
    ∑ m ∈ Finset.range (n + 1), C (p.coeff m) * (rot a b m).2, ?_, ?_⟩
  · have h : (∑ m ∈ Finset.range (n + 1), C (p.coeff m) * (rot a b m).2).natDegree ≤ n - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      rcases m with _ | m
      · simp [rot]
      · have := (rot_natDegree a b m).2.1
        have := Finset.mem_range.mp hm
        omega
    refine lt_of_le_of_lt (degree_le_of_natDegree_le h) ?_
    exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero hn) one_pos
  · intro y z h
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), eval_finsetSum, eval_finsetSum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [rot_eval a b m y z h, eval_mul, eval_mul, eval_C]
    ring

theorem bernstein (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) (θ : ℝ) :
    |sin θ * p.derivative.eval (cos θ)| ≤ n * M := by
  obtain ⟨A, B, hB, hAB⟩ := exists_rot (cos θ) (sin θ) p n hn hp
  have hB1 : B.eval 1 = sin θ * p.derivative.eval (cos θ) := by
    have h1 : HasDerivAt (fun φ : ℝ => p.eval (cos θ * cos φ + sin θ * sin φ))
        (p.derivative.eval (cos θ * cos 0 + sin θ * sin 0) *
          (cos θ * (-sin 0) + sin θ * cos 0)) 0 :=
      (p.hasDerivAt _).comp 0 (((hasDerivAt_cos 0).const_mul _).add ((hasDerivAt_sin 0).const_mul _))
    have h2 : HasDerivAt (fun φ : ℝ => A.eval (cos φ) + sin φ * B.eval (cos φ))
        (A.derivative.eval (cos 0) * (-sin 0) + (cos 0 * B.eval (cos 0) +
          sin 0 * (B.derivative.eval (cos 0) * (-sin 0)))) 0 :=
      ((A.hasDerivAt _).comp 0 (hasDerivAt_cos 0)).add
        ((hasDerivAt_sin 0).mul ((B.hasDerivAt _).comp 0 (hasDerivAt_cos 0)))
    have h3 : (fun φ : ℝ => p.eval (cos θ * cos φ + sin θ * sin φ)) =
        fun φ : ℝ => A.eval (cos φ) + sin φ * B.eval (cos φ) :=
      funext fun φ => hAB _ _ (cos_sq_add_sin_sq φ)
    rw [h3] at h1
    have h4 := h2.unique h1
    simp at h4
    rw [h4]; ring
  rw [← hB1]
  refine schur n hn B hB M (fun k hk => ?_) 1 (fun k hk => ?_) le_rfl
  · have e1 := hAB (cos (th n k)) (sin (th n k)) (cos_sq_add_sin_sq _)
    have e2 := hAB (cos (th n k)) (-sin (th n k)) (by rw [neg_sq]; exact cos_sq_add_sin_sq _)
    have m1 := hM (cos θ * cos (th n k) + sin θ * sin (th n k))
      (by rw [← cos_sub]; exact ⟨neg_one_le_cos _, cos_le_one _⟩)
    have m2 := hM (cos θ * cos (th n k) + sin θ * -sin (th n k))
      (by rw [mul_neg, ← sub_eq_add_neg, ← cos_add]; exact ⟨neg_one_le_cos _, cos_le_one _⟩)
    rw [e1] at m1
    rw [e2] at m2
    rw [abs_le] at m1 m2 ⊢
    constructor <;> linarith [m1.1, m1.2, m2.1, m2.2]
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (th_lt_pi hk).le (th_pos n k hn)

theorem markov_nonneg (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 * M := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  by_cases hy : ∀ k < n, cos (th n k) < x
  · have hd : p.derivative.degree < n := by
      refine lt_of_le_of_lt (degree_le_of_natDegree_le
        ((natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp 1))) ?_
      exact_mod_cast Nat.sub_lt hn0 one_pos
    have := schur n hn p.derivative hd (n * M) (fun k _ => bernstein p n hn hp M hM _) x hy hx1
    calc _ ≤ n * (n * M) := this
      _ = _ := by ring
  · push Not at hy
    obtain ⟨k, hk, hxk⟩ := hy
    have hcos : cos (arccos x) = x := cos_arccos (by linarith) hx1
    have hφ1 : th n k ≤ arccos x := by
      have := arccos_le_arccos hxk
      rwa [arccos_cos (th_pos n k hn).le (th_lt_pi hk).le] at this
    have hφ2 : arccos x ≤ π / 2 := arccos_le_pi_div_two.mpr hx0
    have hth : π / (2 * n) ≤ th n k := by
      unfold th
      gcongr
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [pi_pos]
    have hsin : 1 / (n : ℝ) ≤ sin (arccos x) := by
      have h1 := mul_le_sin (arccos_nonneg x) hφ2
      have h2 : 2 / π * (π / (2 * n)) ≤ 2 / π * arccos x :=
        mul_le_mul_of_nonneg_left (hth.trans hφ1) (by positivity)
      have h3 : 2 / π * (π / (2 * n)) = 1 / (n : ℝ) := by
        have := pi_pos.ne'
        field_simp
      linarith
    have hb := bernstein p n hn hp M hM (arccos x)
    rw [hcos, abs_mul, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 1 / n).trans hsin)] at hb
    have h4 : 1 / (n : ℝ) * |p.derivative.eval x| ≤ n * M :=
      (mul_le_mul_of_nonneg_right hsin (abs_nonneg _)).trans hb
    calc |p.derivative.eval x| = n * (1 / (n : ℝ) * |p.derivative.eval x|) := by field_simp
      _ ≤ n * (n * M) := mul_le_mul_of_nonneg_left h4 hn'.le
      _ = _ := by ring

end Formalism.FourierDecayAlt.P.Markov

namespace Formalism.FourierDecayAlt.P

open Polynomial

theorem markov_inequality : Formalism.FourierDecayAlt.E.AMarkov := by
  intro p d M hp hM x hx
  rcases eq_or_ne d 0 with rfl | hd
  · rw [eq_C_of_natDegree_le_zero hp]; simp
  · rcases le_total 0 x with h | h
    · exact Markov.markov_nonneg p d hd hp M hM x h hx.2
    · have hq : (p.comp (-X)).natDegree ≤ d := by
        refine natDegree_comp_le.trans ?_
        rw [natDegree_neg, natDegree_X, mul_one]; exact hp
      have hMq : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(p.comp (-X)).eval y| ≤ M := by
        intro y hy
        rw [eval_comp]
        refine hM _ ?_
        simp only [eval_neg, eval_X]
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have := Markov.markov_nonneg (p.comp (-X)) d hd hq M hMq (-x) (by linarith) (by linarith [hx.1])
      rw [derivative_comp] at this
      simpa using this

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Markov

open Polynomial

theorem interval_one (hA : Formalism.FourierDecayAlt.E.AMarkov) (P : ℝ[X]) (d : ℕ) (t₀ L M : ℝ) (hL : 0 < L)
    (hd : P.natDegree ≤ d) (hP : ∀ t ∈ Set.Icc t₀ (t₀ + L), |P.eval t| ≤ M) :
    ∀ t ∈ Set.Icc t₀ (t₀ + L), |P.derivative.eval t| ≤ (2 * (d : ℝ) ^ 2 / L) * M := by
  intro t ht
  set l : ℝ[X] := C (t₀ + L / 2) + C (L / 2) * X with hl
  have hldeg : l.natDegree ≤ 1 := by
    rw [hl]; compute_degree
  have hdeg : (P.comp l).natDegree ≤ d := by
    calc (P.comp l).natDegree ≤ P.natDegree * l.natDegree := natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul hd hldeg
      _ = d := mul_one d
  have hleval : ∀ x : ℝ, l.eval x = t₀ + L / 2 + L / 2 * x := by
    intro x; simp [hl]
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(P.comp l).eval x| ≤ M := by
    intro x hx
    rw [eval_comp, hleval]
    apply hP
    constructor <;> nlinarith [hx.1, hx.2]
  set x : ℝ := 2 * (t - t₀) / L - 1 with hx
  have hxm : x ∈ Set.Icc (-1 : ℝ) 1 := by
    have h1 : 0 ≤ 2 * (t - t₀) / L := by
      apply div_nonneg _ hL.le
      linarith [ht.1]
    have h2 : 2 * (t - t₀) / L ≤ 2 := by
      rw [div_le_iff₀ hL]
      linarith [ht.2]
    constructor <;> rw [hx] <;> linarith
  have hlx : l.eval x = t := by
    rw [hleval, hx]; field_simp; ring
  have hder : (P.comp l).derivative.eval x = L / 2 * P.derivative.eval t := by
    rw [derivative_comp, eval_mul, eval_comp, hlx]
    simp [hl]
  have key := hA (P.comp l) d M hdeg hb x hxm
  rw [hder, abs_mul, abs_of_pos (by positivity : 0 < L / 2)] at key
  have : |P.derivative.eval t| ≤ ((d : ℝ) ^ 2 * M) / (L / 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc |P.derivative.eval t| ≤ ((d : ℝ) ^ 2 * M) / (L / 2) := this
    _ = (2 * (d : ℝ) ^ 2 / L) * M := by field_simp

theorem interval_iter (hA : Formalism.FourierDecayAlt.E.AMarkov) (d : ℕ) (t₀ L : ℝ) (hL : 0 < L) (q : ℕ) :
    ∀ (P : ℝ[X]) (M : ℝ), P.natDegree ≤ d → (∀ t ∈ Set.Icc t₀ (t₀ + L), |P.eval t| ≤ M) →
    ∀ t ∈ Set.Icc t₀ (t₀ + L), |(derivative^[q] P).eval t| ≤ (2 * (d : ℝ) ^ 2 / L) ^ q * M := by
  induction q with
  | zero => intro P M _ hP t ht; simpa using hP t ht
  | succ q ih =>
    intro P M hd hP t ht
    rw [Function.iterate_succ_apply]
    have h1 := interval_one hA P d t₀ L M hL hd hP
    have h2 := ih P.derivative ((2 * (d : ℝ) ^ 2 / L) * M)
      ((natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hd)) h1 t ht
    calc _ ≤ _ := h2
      _ = _ := by ring

theorem iteratedDeriv_vec {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type}
    (S : Finset ι) (a : ι → H) (q : ℕ) : ∀ (P : ι → ℝ[X]),
    iteratedDeriv q (fun s : ℝ => ∑ k ∈ S, (P k).eval s • a k) =
      fun s : ℝ => ∑ k ∈ S, (derivative^[q] (P k)).eval s • a k := by
  induction q with
  | zero => intro P; simp
  | succ q ih =>
    intro P
    rw [iteratedDeriv_succ, ih P]
    funext s
    have : HasDerivAt (fun s : ℝ => ∑ k ∈ S, (derivative^[q] (P k)).eval s • a k)
        (∑ k ∈ S, (derivative (derivative^[q] (P k))).eval s • a k) s := by
      apply HasDerivAt.fun_sum
      intro k _
      exact ((derivative^[q] (P k)).hasDerivAt s).smul_const (a k)
    rw [this.deriv]
    simp only [Function.iterate_succ_apply']

end Formalism.FourierDecayAlt.P.Markov

namespace Formalism.FourierDecayAlt.P

open Polynomial

theorem markovVector_of : Formalism.FourierDecayAlt.E.AMarkov → Formalism.FourierDecayAlt.E.MarkovVector := by
  intro hA H _ _ d a t₀ L M hL hM q t ht
  have hF : (fun s : ℝ => ∑ k : Fin (d + 1), s ^ (k : ℕ) • a k) =
      fun s : ℝ => ∑ k : Fin (d + 1), ((X : ℝ[X]) ^ (k : ℕ)).eval s • a k := by
    funext s; simp
  rw [hF, Markov.iteratedDeriv_vec Finset.univ a q (fun k : Fin (d + 1) => (X : ℝ[X]) ^ (k : ℕ))]
  obtain ⟨φ, hφ1, hφ2⟩ := exists_dual_vector'' ℝ
    (∑ k : Fin (d + 1), (derivative^[q] ((X : ℝ[X]) ^ (k : ℕ))).eval t • a k)
  set Q : ℝ[X] := ∑ k : Fin (d + 1), C (φ (a k)) * (X : ℝ[X]) ^ (k : ℕ) with hQ
  have hQdeg : Q.natDegree ≤ d := by
    rw [hQ]
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp k.2)
  have hQeval : ∀ s : ℝ, Q.eval s = φ (∑ k : Fin (d + 1), s ^ (k : ℕ) • a k) := by
    intro s
    rw [hQ, eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, map_smul, smul_eq_mul, mul_comm]
  have hQb : ∀ s ∈ Set.Icc t₀ (t₀ + L), |Q.eval s| ≤ M := by
    intro s hs
    rw [hQeval s, ← Real.norm_eq_abs]
    calc ‖φ (∑ k : Fin (d + 1), s ^ (k : ℕ) • a k)‖
        ≤ ‖φ‖ * ‖∑ k : Fin (d + 1), s ^ (k : ℕ) • a k‖ := φ.le_opNorm _
      _ ≤ 1 * ‖∑ k : Fin (d + 1), s ^ (k : ℕ) • a k‖ := by gcongr
      _ ≤ M := by rw [one_mul]; exact hM s hs
  have hQder : (derivative^[q] Q).eval t =
      φ (∑ k : Fin (d + 1), (derivative^[q] ((X : ℝ[X]) ^ (k : ℕ))).eval t • a k) := by
    rw [hQ, iterate_derivative_sum, eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iterate_derivative_C_mul, eval_mul, eval_C, map_smul, smul_eq_mul, mul_comm]
  have key := Markov.interval_iter hA d t₀ L hL q Q M hQdeg hQb t ht
  rw [hQder, hφ2] at key
  simpa using key

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P

theorem markov_inequality_vector : Formalism.FourierDecayAlt.E.MarkovVector := markovVector_of markov_inequality

end Formalism.FourierDecayAlt.P
