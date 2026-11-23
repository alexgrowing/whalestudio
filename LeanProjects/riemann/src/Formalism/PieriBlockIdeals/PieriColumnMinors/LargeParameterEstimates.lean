import Formalism.PieriBlockIdeals.TailInequalityEventually
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkage

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.LargeParameterEstimates

open Classical
open Formalism.CohomologicalDescent.LogSmallConstantBounds

structure ParameterBounds (P : Par) (X' A : ℝ) : Prop where
  b_pos : 0 < P.b
  X_pos : 0 < X'
  A_ge : 1 ≤ A
  x_ge : 5 ≤ P.x
  L_ge : 4 ≤ P.L
  n1 : (1 : ℝ) ≤ P.n
  m2 : (2 : ℝ) ≤ P.m
  nA : (P.n : ℝ) ≤ A
  kA : (P.k : ℝ) ≤ A
  fA : (P.f : ℝ) ≤ A
  tA : (P.t : ℝ) ≤ A
  t1 : (1 : ℝ) ≤ P.t
  Nr2 : (P.Nr : ℝ) ≤ 2 * P.t
  f2n : (P.f : ℝ) = 2 * P.n
  S1 : 1 ≤ P.S
  tη : (P.t : ℝ) ≤ P.η

theorem large_parameter_facts_of_hyp {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A) (hB : Big P.L P.x X' A) :
    ParameterBounds P X' A := by
  have hX1 := hB.X1
  have hL := hB.L_ge
  have htA := hR.t_le
  have h1 := hH.t_ge
  have h2 := hR.f_le
  have h3 := hR.f_eq
  have h4 := hH.Nr_eq
  have h5 := hH.m_pos
  have hnt : P.n ≤ P.t := by omega
  have hkt : P.k ≤ P.t := by omega
  have hft : P.f ≤ P.t := by omega
  have ht1 : 1 ≤ P.t := by omega
  have hNr : P.Nr ≤ 2 * P.t := by omega
  have hnt' : (P.n : ℝ) ≤ P.t := by exact_mod_cast hnt
  have hkt' : (P.k : ℝ) ≤ P.t := by exact_mod_cast hkt
  have hft' : (P.f : ℝ) ≤ P.t := by exact_mod_cast hft
  have ht1' : (1 : ℝ) ≤ P.t := by exact_mod_cast ht1
  have hNr' : (P.Nr : ℝ) ≤ 2 * P.t := by exact_mod_cast hNr
  exact ⟨Real.exp_pos _, by linarith, by linarith, hB.x_ge, hB.L_ge,
    by exact_mod_cast hH.n_pos, by exact_mod_cast hR.m_ge, by linarith, by linarith,
    by linarith, htA, ht1', hNr', by exact_mod_cast h3, hR.S_ge, hH.t_le⟩

theorem eventually_power_le_exp_power (c a δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop, c * x ^ a ≤ Real.exp (x ^ δ) := by
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ δ) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hδ
  have h3 := ((tendsto_exp_div_rpow_atTop (a / δ)).comp h1).eventually_ge_atTop (|c| + 1)
  filter_upwards [h3, Filter.eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hx' : |c| + 1 ≤ Real.exp (x ^ δ) / (x ^ δ) ^ (a / δ) := hx
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hpow : (x ^ δ) ^ (a / δ) = x ^ a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  rw [hpow] at hx'
  have hxa : 0 < x ^ a := by positivity
  rw [le_div_iff₀ hxa] at hx'
  have hc : c * x ^ a ≤ (|c| + 1) * x ^ a :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hxa.le
  linarith

private theorem rpow_add_mul_eq_pow_mul_pow (x C e : ℝ) (hx : 0 < x) (p q r : ℕ) :
    x ^ (C * (p : ℝ) + (q : ℝ) + e * (r : ℝ)) = (x ^ C) ^ p * x ^ q * (x ^ e) ^ r := by
  rw [Real.rpow_add hx, Real.rpow_add hx, Real.rpow_mul hx.le, Real.rpow_mul hx.le,
    Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]

private theorem eventually_mul_pow_le_exp_rpow (c C e δ : ℝ) (hδ : 0 < δ) (p q r : ℕ) :
    ∀ᶠ x : ℝ in Filter.atTop, c * ((x ^ C) ^ p * x ^ q * (x ^ e) ^ r) ≤ Real.exp (x ^ δ) := by
  filter_upwards [eventually_power_le_exp_power c (C * (p : ℝ) + (q : ℝ) + e * (r : ℝ)) δ hδ,
    Filter.eventually_gt_atTop (0 : ℝ)] with x h hx
  rwa [rpow_add_mul_eq_pow_mul_pow x C e hx p q r] at h

theorem eventually_large_parameter_bound : BigEv := by
  intro ε C hε
  have hε3 : 0 < ε / 3 := by positivity
  have e1 := Filter.eventually_ge_atTop (5 : ℝ)
  have e2 := (tendsto_rpow_atTop hε).eventually_ge_atTop (4 : ℝ)
  have e3 := eventually_power_le_exp_power 12 ε (ε / 3) hε3
  have e4 := eventually_mul_pow_le_exp_rpow 5.2 C 0 (ε / 3) hε3 3 1 0
  have e5 := eventually_mul_pow_le_exp_rpow 40 C ε (ε / 3) hε3 7 2 1
  have e6 := eventually_mul_pow_le_exp_rpow 40 C ε ε hε 7 2 3
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx0 x hx
  have h2' : (4 : ℝ) ≤ x ^ ε := h2
  refine ⟨h1, h2', ?_, ?_, ?_, ?_⟩
  · linarith
  · have e : (5.2 : ℝ) * (x ^ C) ^ 3 * x = 5.2 * ((x ^ C) ^ 3 * x ^ 1 * (x ^ (0 : ℝ)) ^ 0) := by
      ring
    linarith
  · have e : (40 : ℝ) * (x ^ C) ^ 7 * x ^ 2 * x ^ ε = 40 * ((x ^ C) ^ 7 * x ^ 2 * (x ^ ε) ^ 1) := by
      ring
    linarith
  · have e : (40 : ℝ) * (x ^ C) ^ 7 * x ^ 2 * (x ^ ε) ^ 3
        = 40 * ((x ^ C) ^ 7 * x ^ 2 * (x ^ ε) ^ 3) := by ring
    linarith

private theorem pow_le_pow_add_of_one_le {A : ℝ} (hA : 1 ≤ A) (i k : ℕ) : A ^ i ≤ A ^ (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ]
    nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ A) (i + k)) (sub_nonneg.2 hA)]

theorem polynomial_inequality_large_x (A x L S t : ℝ) (hA : 1 ≤ A) (hx : 5 ≤ x) (hL : 4 ≤ L) (hS : 0 ≤ S)
    (ht : t ≤ A) :
    4 * A ^ 4 * x * L ^ 2 + 2 * A ^ 3 * (S + t + L) + t ≤ A ^ 4 * x ^ 2 * (L ^ 2 + S) := by
  have hA0 : 0 ≤ A := by linarith
  have hA3 : 1 ≤ A ^ 3 := by simpa using pow_le_pow_add_of_one_le hA 0 3
  have h34 : A ^ 3 ≤ A ^ 4 := pow_le_pow_add_of_one_le hA 3 1
  have hA4 : A ≤ A ^ 4 := by simpa using pow_le_pow_add_of_one_le hA 1 3
  have hat : A ^ 3 * t ≤ A ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left ht (by linarith : (0 : ℝ) ≤ A ^ 3)]
  have hL0 : 0 ≤ L := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hA40 : 0 ≤ A ^ 4 := by positivity
  have p1 : 0 ≤ A ^ 4 * L ^ 2 * (x * (x - 5)) :=
    mul_nonneg (by positivity) (mul_nonneg hx0 (by linarith))
  have hx25 : 0 ≤ x ^ 2 - 25 := by nlinarith
  have p2 : 0 ≤ S * (A ^ 4 * x ^ 2 - 2 * A ^ 3) := by
    apply mul_nonneg hS
    nlinarith [mul_nonneg (sub_nonneg.2 h34) (sq_nonneg x),
      mul_nonneg (by linarith : (0 : ℝ) ≤ A ^ 3) hx25]
  have hxL : 0 ≤ x * L - 20 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hL)]
  have p3 : 0 ≤ A ^ 4 * (L * (x * L - 20)) := mul_nonneg hA40 (mul_nonneg hL0 hxL)
  have p4 : 0 ≤ (A ^ 4 - A ^ 3) * L := mul_nonneg (by linarith) hL0
  have p5 : 0 ≤ A ^ 4 * (L - 4) := mul_nonneg hA40 (by linarith)
  nlinarith [p1, p2, p3, p4, p5, hat, hA4, ht]

theorem maximal_index_size_bound : KmaxSize := by
  intro P X' A hH hR hB
  have F := large_parameter_facts_of_hyp hH hR hB
  have hb := F.b_pos
  have hm : (0 : ℝ) < P.m := by linarith [F.m2]
  have hn : (0 : ℝ) < P.n := by linarith [F.n1]
  have ht : (0 : ℝ) < P.t := by linarith [F.t1]
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hLp : 0 < P.L := by linarith [F.L_ge]
  have hS0 : 0 ≤ P.S := by linarith [F.S1]
  have hA0 : 0 ≤ A := by linarith [F.A_ge]
  have hx0 : 0 ≤ P.x := by linarith [F.x_ge]
  have hN0 : 0 ≤ P.N := by unfold Par.N; positivity
  have hNt0 : 0 < P.N + (P.t : ℝ) := by linarith
  have hD1pos : 0 < (P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2 :=
    mul_pos (mul_pos (mul_pos hn (pow_pos ht 2)) hNt0) (pow_pos hLp 2)
  have hD2 : 0 ≤ (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L) :=
    mul_nonneg (mul_nonneg hk0 (sq_nonneg _)) (by linarith)
  have hDpos : 0 < (P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
      + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L) := by linarith
  have hbD : 2 * P.b / P.lstar = 2 * ((P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
      + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L)) / (P.m : ℝ) := by
    unfold Par.lstar
    field_simp
    try ring
  have hnA := F.nA
  have hkA := F.kA
  have htA := F.tA
  have htt : (P.t : ℝ) ^ 2 ≤ A ^ 2 := by nlinarith [mul_le_mul htA htA ht.le hA0]
  have hnn : (P.n : ℝ) ^ 2 ≤ A ^ 2 := by nlinarith [mul_le_mul hnA hnA hn.le hA0]
  have hnt2 : (P.n : ℝ) * (P.t : ℝ) ^ 2 ≤ A ^ 3 := by
    nlinarith [mul_le_mul hnA htt (sq_nonneg _) hA0]
  have hkn2 : (P.k : ℝ) * (P.n : ℝ) ^ 2 ≤ A ^ 3 := by
    nlinarith [mul_le_mul hkA hnn (sq_nonneg _) hA0]
  have hNt : P.N + (P.t : ℝ) ≤ 2 * A * P.x := by
    nlinarith [hR.N_le, mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ P.x by linarith [F.x_ge]) hA0]
  have hD1 : (P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
      ≤ A ^ 3 * (2 * A * P.x) * P.L ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul hnt2 hNt hNt0.le (pow_nonneg hA0 3)) (sq_nonneg _)
  have hD2' : (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L)
      ≤ A ^ 3 * (P.S + (P.t : ℝ) + P.L) :=
    mul_le_mul_of_nonneg_right hkn2 (by linarith)
  have hDm : 2 * ((P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
      + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L)) / (P.m : ℝ)
      ≤ (P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
      + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L) := by
    rw [div_le_iff₀ hm]
    nlinarith [mul_le_mul_of_nonneg_left F.m2 hDpos.le]
  have q1 : 0 ≤ A ^ 4 * P.x * P.L ^ 2 := mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hx0) (sq_nonneg _)
  have q2 : 0 ≤ A ^ 3 * (P.S + (P.t : ℝ) + P.L) := mul_nonneg (pow_nonneg hA0 3) (by linarith)
  have hc : 2 * P.b / P.lstar
      ≤ 4 * A ^ 4 * P.x * P.L ^ 2 + 2 * A ^ 3 * (P.S + (P.t : ℝ) + P.L) := by
    rw [hbD]; nlinarith [hD1, hD2', hDm, q1, q2]
  have hfin := polynomial_inequality_large_x A P.x P.L P.S P.t F.A_ge F.x_ge F.L_ge hS0 htA
  have h0 : 0 ≤ 2 * P.b / P.lstar := by
    rw [hbD]; exact div_nonneg (by linarith) hm.le
  have ha : (P.kmax : ℝ) ≤ 2 * P.b / P.lstar := by
    unfold Par.kmax; exact Nat.floor_le h0
  exact ⟨ha, hbD, hc, by linarith, by linarith⟩

theorem n_mul_width_eq_b_div {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A) (hB : Big P.L P.x X' A) :
    (P.n : ℝ) * P.w'' = P.b / X' := by
  have F := large_parameter_facts_of_hyp hH hR hB
  have hx : (0 : ℝ) < P.x := by linarith [F.x_ge]
  have hn : (0 : ℝ) < P.n := by linarith [F.n1]
  have hX := F.X_pos
  unfold Par.w''
  rw [hR.b'_eq]
  field_simp
  try ring

theorem small_term_bound_first : Small1 := by
  intro P X' A T hH hR hB hT
  have F := large_parameter_facts_of_hyp hH hR hB
  have hb := F.b_pos
  have hX := F.X_pos
  have hn : (0 : ℝ) < P.n := by linarith [F.n1]
  have hx : (0 : ℝ) < P.x := by linarith [F.x_ge]
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hw := n_mul_width_eq_b_div hH hR hB
  have hkS := hR.kS_le
  have h1 : (P.k : ℝ) * (P.S + 1) ≤ 2 * (P.k : ℝ) * P.S := by
    nlinarith [mul_nonneg hk0 (sub_nonneg.2 F.S1)]
  have h2 : 2 * (P.k : ℝ) * P.S ≤ 2 * P.w'' := by linarith
  have h3 : 2 * P.w'' = 2 * P.b / ((P.n : ℝ) * X') := by
    unfold Par.w''
    rw [hR.b'_eq]
    field_simp
    try ring
  have hT' : (T : ℝ) ≤ 2 * (P.n : ℝ) := by
    have : (T : ℝ) ≤ P.f := by exact_mod_cast hT
    linarith [F.f2n]
  have hL2 : 0 ≤ P.L + 2 := by linarith [F.L_ge]
  have hw0 : 0 ≤ P.w'' := by
    nlinarith [mul_nonneg hk0 (by linarith [F.S1] : (0 : ℝ) ≤ P.S)]
  have s1 : 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) ≤ 4 * P.w'' * (P.L + 2) := by
    nlinarith [mul_le_mul_of_nonneg_right (h1.trans h2) hL2]
  have s2 : (T : ℝ) * (2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2))
      ≤ (T : ℝ) * (4 * P.w'' * (P.L + 2)) :=
    mul_le_mul_of_nonneg_left s1 (Nat.cast_nonneg _)
  have s3 : (T : ℝ) * (4 * P.w'' * (P.L + 2)) ≤ (2 * (P.n : ℝ)) * (4 * P.w'' * (P.L + 2)) :=
    mul_le_mul_of_nonneg_right hT' (mul_nonneg (mul_nonneg (by norm_num) hw0) hL2)
  have s4 : (2 * (P.n : ℝ)) * (4 * P.w'' * (P.L + 2)) = 8 * (P.L + 2) * P.b / X' := by
    rw [mul_div_assoc, ← hw]; ring
  have h5 : 8 * (P.L + 2) * P.b / X' ≤ 2 * P.b := by
    rw [div_le_iff₀ hX]
    nlinarith [mul_le_mul_of_nonneg_left hB.X1 hb.le]
  exact ⟨h1, h2, h3, by linarith, h5⟩

theorem small_term_bound_second : Small2 := by
  intro P X' A hH hR hB
  have F := large_parameter_facts_of_hyp hH hR hB
  have hb := F.b_pos
  have hX := F.X_pos
  have hb' : 0 < P.b' := hH.b'_pos
  have hf0 : (0 : ℝ) ≤ P.f := Nat.cast_nonneg _
  have hNr0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hA0 : 0 ≤ A := by linarith [F.A_ge]
  have hNr2 : (P.Nr : ℝ) ^ 2 ≤ 4 * (P.t : ℝ) ^ 2 := by
    nlinarith [mul_le_mul F.Nr2 F.Nr2 hNr0 (by linarith)]
  have e1 : 1.3 * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.b' ≤ 5.2 * (P.f : ℝ) * (P.t : ℝ) ^ 2 * P.b' := by
    nlinarith [mul_le_mul_of_nonneg_left hNr2 (mul_nonneg hf0 hb'.le)]
  have htt : (P.t : ℝ) ^ 2 ≤ A ^ 2 := by nlinarith [mul_le_mul F.tA F.tA ht0 hA0]
  have hft : (P.f : ℝ) * (P.t : ℝ) ^ 2 ≤ A ^ 3 := by
    nlinarith [mul_le_mul F.fA htt (sq_nonneg _) hA0]
  have eb : 5.2 * A ^ 3 * P.x * P.b / X' = 5.2 * A ^ 3 * P.b' := by
    rw [hR.b'_eq]; ring
  have e2 : 5.2 * (P.f : ℝ) * (P.t : ℝ) ^ 2 * P.b' ≤ 5.2 * A ^ 3 * P.x * P.b / X' := by
    rw [eb]; nlinarith [mul_le_mul_of_nonneg_right hft hb'.le]
  have e3 : 5.2 * A ^ 3 * P.x * P.b / X' ≤ P.b := by
    rw [div_le_iff₀ hX]
    nlinarith [mul_le_mul_of_nonneg_left hB.X2 hb.le]
  exact ⟨e1, e2, e3⟩

theorem small_term_bound_third : Small3 := by
  intro P X' A hH hR hB
  have F := large_parameter_facts_of_hyp hH hR hB
  have hb := F.b_pos
  have hX := F.X_pos
  have hA0 : 0 ≤ A := by linarith [F.A_ge]
  have hx0 : 0 ≤ P.x := by linarith [F.x_ge]
  have hL0 : 0 ≤ P.L := by linarith [F.L_ge]
  have hS0 : 0 ≤ P.S := by linarith [F.S1]
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ P.f := Nat.cast_nonneg _
  have hNr0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
  have hkm0 : (0 : ℝ) ≤ P.kmax := Nat.cast_nonneg _
  have hη : (P.t : ℝ) ≤ P.η := F.tη
  have c1 : P.S + P.η ≤ P.b / X' := by
    rw [le_div_iff₀ hX]; linarith [hR.sum_le]
  have hB0 : 0 ≤ P.b / X' := div_nonneg hb.le hX.le
  have hK := (maximal_index_size_bound P X' A hH hR hB).2.2.2.2
  have hA4 : 1 ≤ A ^ 4 := by simpa using pow_le_pow_add_of_one_le F.A_ge 0 4
  have hx2 : 25 ≤ P.x ^ 2 := by nlinarith [F.x_ge]
  have hq : 25 ≤ A ^ 4 * P.x ^ 2 := by
    nlinarith [mul_le_mul hA4 hx2 (by norm_num) (by positivity)]
  have hq0 : 0 ≤ A ^ 4 * P.x ^ 2 := by positivity
  have hSB : P.S ≤ P.b / X' := by linarith
  have hL16 : 16 ≤ P.L ^ 2 := by nlinarith [mul_le_mul F.L_ge F.L_ge (by norm_num) hL0]
  have c2 : P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6
      ≤ 5 * A ^ 4 * P.x ^ 2 * (P.L ^ 2 + P.b / X') := by
    nlinarith [mul_le_mul_of_nonneg_left hSB hq0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ A ^ 4 * P.x ^ 2 - 1) hB0,
      mul_le_mul_of_nonneg_right hq (sq_nonneg P.L)]
  have hNrA : (P.Nr : ℝ) ≤ 2 * A := by linarith [F.Nr2, F.tA]
  have hNr2 : (P.Nr : ℝ) ^ 2 ≤ 4 * A ^ 2 := by
    nlinarith [mul_le_mul hNrA hNrA hNr0 (by linarith)]
  have hfN : (P.f : ℝ) * (P.Nr : ℝ) ^ 2 ≤ 4 * A ^ 3 := by
    nlinarith [mul_le_mul F.fA hNr2 (sq_nonneg _) hA0]
  have c3 : (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L ≤ 4 * A ^ 3 * P.L :=
    mul_le_mul_of_nonneg_right hfN hL0
  have c4 : (P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6) * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L ≤
      20 * A ^ 7 * P.x ^ 2 * P.L * (P.L ^ 2 + P.b / X') := by
    have hpos : 0 ≤ (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L :=
      mul_nonneg (mul_nonneg hf0 (sq_nonneg _)) hL0
    have hpos2 : 0 ≤ 5 * A ^ 4 * P.x ^ 2 * (P.L ^ 2 + P.b / X') :=
      mul_nonneg (by positivity) (by positivity)
    nlinarith [mul_le_mul c2 c3 hpos hpos2]
  have hbb : P.b = Real.exp P.L := rfl
  have hXB : X' * (P.b / X') = P.b := by field_simp
  have c5 : 20 * A ^ 7 * P.x ^ 2 * P.L * (P.L ^ 2 + P.b / X') ≤ P.b := by
    nlinarith [hB.b3, mul_le_mul_of_nonneg_right hB.X3 hB0]
  exact ⟨c1, c2, c3, c4, c5⟩

theorem sum_of_small_terms_bound : SmallSum := by
  intro P X' A T hH hR hB hT
  have F := large_parameter_facts_of_hyp hH hR hB
  have hb := F.b_pos
  obtain ⟨-, -, -, a4, a5⟩ := small_term_bound_first P X' A T hH hR hB hT
  obtain ⟨b1, b2, b3⟩ := small_term_bound_second P X' A hH hR hB
  obtain ⟨-, -, -, c4, c5⟩ := small_term_bound_third P X' A hH hR hB
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left F.m2 hb.le]

theorem tail_bound_holds : TailInequalitySum := by
  intro P X' A T hH hR hB hT
  have h := sum_of_small_terms_bound P X' A T hH hR hB hT
  unfold totalBound
  nlinarith [h.1, h.2]

theorem eventually_power_le_exp_mul_power (c a β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop, c * x ^ a ≤ Real.exp (β * x ^ δ) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have e1 := eventually_power_le_exp_power c a (δ / 2) hδ2
  have e2 := (tendsto_rpow_atTop hδ2).eventually_ge_atTop (1 / β)
  filter_upwards [e1, e2, Filter.eventually_gt_atTop (0 : ℝ)] with x h1 h2 hx0
  have h2' : 1 / β ≤ x ^ (δ / 2) := h2
  have hy : 0 < x ^ (δ / 2) := by positivity
  have hsplit : x ^ δ = x ^ (δ / 2) * x ^ (δ / 2) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have h3 : 1 ≤ β * x ^ (δ / 2) := by
    have := mul_le_mul_of_nonneg_left h2' hβ.le
    rwa [mul_one_div_cancel hβ.ne'] at this
  have h4 : x ^ (δ / 2) ≤ β * x ^ δ := by
    rw [hsplit]; nlinarith [mul_le_mul_of_nonneg_left h3 hy.le]
  exact h1.trans (Real.exp_le_exp.2 h4)

theorem forty_eight_k_sq_t_sq_lt_b {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A)
    (hB : Big P.L P.x X' A) : 48 * (P.k : ℝ) ^ 2 * (P.t : ℝ) ^ 2 < P.b := by
  have F := large_parameter_facts_of_hyp hH hR hB
  have hA0 : 0 ≤ A := by linarith [F.A_ge]
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hx0 : 0 ≤ P.x := by linarith [F.x_ge]
  have hL0 : 0 ≤ P.L := by linarith [F.L_ge]
  have hkt : (P.k : ℝ) * P.t ≤ A ^ 2 := by nlinarith [mul_le_mul F.kA F.tA ht0 hA0]
  have hkt2 : ((P.k : ℝ) * P.t) * ((P.k : ℝ) * P.t) ≤ A ^ 2 * A ^ 2 :=
    mul_le_mul hkt hkt (mul_nonneg hk0 ht0) (by positivity)
  have h47 : A ^ 4 ≤ A ^ 7 := pow_le_pow_add_of_one_le F.A_ge 4 3
  have hA4 : 1 ≤ A ^ 4 := by simpa using pow_le_pow_add_of_one_le F.A_ge 0 4
  have hx2 : 25 ≤ P.x ^ 2 := by nlinarith [F.x_ge]
  have hL2 : 16 ≤ P.L ^ 2 := by nlinarith [mul_le_mul F.L_ge F.L_ge (by norm_num) hL0]
  have hL3 : 64 ≤ P.L ^ 3 := by nlinarith [mul_le_mul F.L_ge hL2 (by norm_num) hL0]
  have p1 : A ^ 4 * 25 ≤ A ^ 7 * P.x ^ 2 := mul_le_mul h47 hx2 (by norm_num) (by positivity)
  have p2 : A ^ 4 * 25 * 64 ≤ A ^ 7 * P.x ^ 2 * P.L ^ 3 :=
    mul_le_mul p1 hL3 (by norm_num) (by positivity)
  have hbb : P.b = Real.exp P.L := rfl
  nlinarith [hB.b3]

theorem twelve_k_t_mul_lt_b {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A)
    (hB : Big P.L P.x X' A) : 12 * (P.k : ℝ) * (P.t : ℝ) * P.b' < P.b := by
  have F := large_parameter_facts_of_hyp hH hR hB
  have hb := F.b_pos
  have hX := F.X_pos
  have hA0 : 0 ≤ A := by linarith [F.A_ge]
  have hx0 : 0 < P.x := by linarith [F.x_ge]
  have hL0 : 0 ≤ P.L := by linarith [F.L_ge]
  have ht0 : (0 : ℝ) ≤ P.t := Nat.cast_nonneg _
  have hkt : (P.k : ℝ) * P.t ≤ A ^ 2 := by nlinarith [mul_le_mul F.kA F.tA ht0 hA0]
  have h27 : A ^ 2 ≤ A ^ 7 := pow_le_pow_add_of_one_le F.A_ge 2 5
  have hA2 : 1 ≤ A ^ 2 := by simpa using pow_le_pow_add_of_one_le F.A_ge 0 2
  have hxL : 20 ≤ P.x * P.L := by
    nlinarith [mul_le_mul F.x_ge F.L_ge (by norm_num) hx0.le]
  have key : 12 * (P.k : ℝ) * P.t * P.x < X' := by
    have p1 : (P.k : ℝ) * P.t * P.x ≤ A ^ 2 * P.x := mul_le_mul_of_nonneg_right hkt hx0.le
    have p2 : A ^ 2 * (P.x * (P.x * P.L)) ≤ A ^ 7 * (P.x * (P.x * P.L)) :=
      mul_le_mul_of_nonneg_right h27 (by positivity)
    have p3 : A ^ 2 * P.x * 20 ≤ A ^ 2 * P.x * (P.x * P.L) :=
      mul_le_mul_of_nonneg_left hxL (by positivity)
    have p4 : 0 < A ^ 2 * P.x := by positivity
    nlinarith [hB.X3]
  calc 12 * (P.k : ℝ) * P.t * P.b' = 12 * (P.k : ℝ) * P.t * P.x * P.b / X' := by
        rw [hR.b'_eq]; ring
    _ < P.b := by
        rw [div_lt_iff₀ hX]
        nlinarith [mul_lt_mul_of_pos_right key hb]

theorem double_length_bound_lt_width {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A)
    (hB : Big P.L P.x X' A) (hw45 : P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S)
    (hbig : 4 * A ^ 4 * P.x ^ 2 * P.L ^ 2 < P.b ^ ((4 : ℝ) / 5)) :
    2 * (2 * P.b / P.lstar + (P.t : ℝ)) < P.w'' := by
  have F := large_parameter_facts_of_hyp hH hR hB
  have hS : 0 < P.S := by linarith [F.S1]
  have h1 : P.b ^ ((4 : ℝ) / 5) * P.S ≤ P.w'' := (le_div_iff₀ hS).1 hw45
  have h2 := mul_lt_mul_of_pos_right hbig hS
  have hK := (maximal_index_size_bound P X' A hH hR hB).2.2.2.1
  have q0 : 0 ≤ A ^ 4 * P.x ^ 2 := by positivity
  have hL2 : 1 ≤ P.L ^ 2 := by nlinarith [F.L_ge]
  have h3 := mul_nonneg q0 (mul_nonneg (sq_nonneg P.L) (sub_nonneg.2 F.S1))
  have h4 := mul_nonneg q0 (mul_nonneg hS.le (sub_nonneg.2 hL2))
  nlinarith [h1, h2, hK, h3, h4]

theorem top_level_sum_le_two_b {P : Par} {X' A : ℝ} (hH : P.Hyp) (hR : Rows P X' A)
    (hB : Big P.L P.x X' A) :
    P.S + P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) + P.η + ((P.t : ℝ) - 1) / 2 ≤ 2 * P.b' := by
  have F := large_parameter_facts_of_hyp hH hR hB
  have hb := F.b_pos
  have hX := F.X_pos
  have hx0 : 0 < P.x := by linarith [F.x_ge]
  have hb'0 : 0 < P.b' := hH.b'_pos
  have hS0 : 0 ≤ P.S := by linarith [F.S1]
  have hSη : P.S + P.η ≤ P.b / X' := by
    rw [le_div_iff₀ hX]; linarith [hR.sum_le]
  have hB0 : 0 ≤ P.b / X' := div_nonneg hb.le hX.le
  have hb'e : P.b' = P.x * (P.b / X') := by rw [hR.b'_eq]; ring
  have h5B : 5 * (P.b / X') ≤ P.b' := by
    rw [hb'e]; nlinarith [mul_le_mul_of_nonneg_right F.x_ge hB0]
  have h1x : 1 / P.x ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) F.x_ge
  have h1x2 : 1 / P.x ^ 2 ≤ 1 / 25 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith [F.x_ge])
  have e1 := mul_le_mul_of_nonneg_left h1x hb'0.le
  have e2 := mul_le_mul_of_nonneg_left h1x2 hb'0.le
  have hη := F.tη
  nlinarith [e1, e2]

theorem large_bound_of_constraints : LargeOfRows := by
  intro P X' A hH hR hB hw hbig
  exact ⟨hB.L_ge, forty_eight_k_sq_t_sq_lt_b hH hR hB, twelve_k_t_mul_lt_b hH hR hB, double_length_bound_lt_width hH hR hB hw hbig,
    top_level_sum_le_two_b hH hR hB⟩

end Formalism.CohomologicalDescent.LargeParameterEstimates
