import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

noncomputable section

open Matrix GlobalTheory.PsCo.Pc1
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc3

variable {n : ℕ}

def prP (ε : Fin n → Bool) : Mat n := diagonal fun i => if ε i then 1 else 0

def sgM (ε : Fin n → Bool) : Mat n := diagonal fun i => if ε i then 1 else -1

def bExt (ε : Fin n → Bool) (B : Mode ε → ℂ) (p : Fin n × Fin n) : ℂ :=
  if h : ε p.1 = true ∧ ε p.2 = false then B ⟨p, h⟩ else 0

theorem sum_mode (ε : Fin n → Bool) (g : Fin n × Fin n → ℂ) :
    ∑ x : Mode ε, g x.1 = ∑ i, ∑ j, if ε i = true ∧ ε j = false then g (i, j) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false)
    (by simp) g, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

theorem sum_mode_re (ε : Fin n → Bool) (g : Fin n × Fin n → ℝ) :
    ∑ x : Mode ε, g x.1 = ∑ i, ∑ j, if ε i = true ∧ ε j = false then g (i, j) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false)
    (by simp) g, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

theorem prP_mul_pB_apply (ε : Fin n → Bool) (B : Mode ε → ℂ) (i j : Fin n) :
    (prP ε * pB ε B) i j = if ε i = true ∧ ε j = false then bExt ε B (i, j) else 0 := by
  simp only [prP, diagonal_mul, pB, bExt]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem trace_projection_mul_modeMatrix_mul (ε : Fin n → Bool) (B : Mode ε → ℂ) (M : Mat n) :
    trace (prP ε * pB ε B * M) = ∑ x : Mode ε, B x * M x.1.2 x.1.1 := by
  have : ∀ x : Mode ε, B x * M x.1.2 x.1.1 = (fun p : Fin n × Fin n => bExt ε B p * M p.2 p.1) x.1 := by
    intro x; simp [bExt, x.2]
  rw [Finset.sum_congr rfl fun x _ => this x, sum_mode ε (fun p : Fin n × Fin n => bExt ε B p * M p.2 p.1)]
  simp only [trace, diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply (M := prP ε * pB ε B)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prP_mul_pB_apply]
  split_ifs <;> simp

theorem pB_apply_swap (ε : Fin n → Bool) (B : Mode ε → ℂ) (i j : Fin n) :
    pB ε B j i = star (pB ε B i j) := by
  simp only [pB]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem pB_isHermitian (ε : Fin n → Bool) (B : Mode ε → ℂ) : (pB ε B).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply]
  rw [pB_apply_swap ε B j i]

theorem trace_projection_mul_modeMatrix_mul_self (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    trace (prP ε * pB ε B * pB ε B) = ((∑ x, ‖B x‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_projection_mul_modeMatrix_mul]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pB_apply_swap]
  have : pB ε B x.1.1 x.1.2 = B x := by simp [pB, x.2.1, x.2.2]
  rw [this, show star (B x) = conj (B x) from rfl, Complex.mul_conj']

theorem sgM_mul_sgM (ε : Fin n → Bool) : sgM ε * sgM ε = 1 := by
  rw [sgM, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; split_ifs <;> simp

theorem sgM_pB_sgM (ε : Fin n → Bool) (B : Mode ε → ℂ) : sgM ε * pB ε B * sgM ε = -pB ε B := by
  ext i j
  simp only [sgM, diagonal_mul, mul_diagonal, Matrix.neg_apply]
  simp only [pB]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem sgM_prP (ε : Fin n → Bool) : sgM ε * prP ε = prP ε * sgM ε := by
  simp only [sgM, prP, diagonal_mul_diagonal, mul_comm]

theorem exp_neg_pB (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    NormedSpace.exp (-pB ε B) = sgM ε * NormedSpace.exp (pB ε B) * sgM ε := by
  have hu : IsUnit (sgM ε) := ⟨⟨sgM ε, sgM ε, sgM_mul_sgM ε, sgM_mul_sgM ε⟩, rfl⟩
  have hinv : (sgM ε)⁻¹ = sgM ε := inv_eq_left_inv (sgM_mul_sgM ε)
  calc NormedSpace.exp (-pB ε B) = NormedSpace.exp (sgM ε * pB ε B * (sgM ε)⁻¹) := by rw [hinv, sgM_pB_sgM]
    _ = sgM ε * NormedSpace.exp (pB ε B) * (sgM ε)⁻¹ := Matrix.exp_conj _ _ hu
    _ = _ := by rw [hinv]

theorem trace_neg_side (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B)) = -trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) := by
  have hS := sgM_mul_sgM ε
  have hP : prP ε * sgM ε = sgM ε * prP ε := (sgM_prP ε).symm
  have h1 : prP ε * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε) =
      (sgM ε * (prP ε * (sgM ε * pB ε B * sgM ε) * NormedSpace.exp (pB ε B))) * sgM ε := by
    calc prP ε * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε)
        = prP ε * (sgM ε * sgM ε) * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε) := by rw [hS, mul_one]
      _ = (prP ε * sgM ε) * (sgM ε * pB ε B * sgM ε) * NormedSpace.exp (pB ε B) * sgM ε := by
        simp only [mul_assoc]
      _ = _ := by rw [hP]; simp only [mul_assoc]
  rw [exp_neg_pB, h1, trace_mul_comm, ← mul_assoc, hS, one_mul, sgM_pB_sgM]
  simp [trace_neg]

theorem trace_conj_diag (U : Mat n) (hU : star U * U = 1) (A : Mat n) (v : Fin n → ℂ) :
    trace (A * (U * diagonal v * star U)) = ∑ i, (star U * A * U) i i * v i := by
  have : A * (U * diagonal v * star U) = (A * U * diagonal v) * star U := by simp only [mul_assoc]
  rw [this, trace_mul_comm, ← mul_assoc, ← mul_assoc]
  simp only [trace, diag, mul_diagonal]

theorem conjDiag_re_nonneg (U : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (i : Fin n) :
    ∃ c : ℝ, 0 ≤ c ∧ (star U * prP ε * U) i i = c := by
  refine ⟨∑ k, (if ε k then 1 else 0) * ‖U k i‖ ^ 2, Finset.sum_nonneg fun k _ => by positivity, ?_⟩
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [prP, Matrix.mul_diagonal, Matrix.star_apply, show star (U k i) = conj (U k i) from rfl]
  split_ifs
  · rw [mul_one, mul_comm, Complex.mul_conj']; push_cast; ring
  · simp

theorem re_term (c l : ℝ) (hc : 0 ≤ c) :
    2 * (((c : ℂ) * ((l : ℂ) * (l : ℂ))).re) ≤
      ((c : ℂ) * ((l : ℂ) * Complex.exp l)).re - ((c : ℂ) * ((l : ℂ) * Complex.exp (-l))).re := by
  have h1 : ((c : ℂ) * ((l : ℂ) * (l : ℂ))).re = c * (l * l) := by norm_cast
  have h2 : ((c : ℂ) * ((l : ℂ) * Complex.exp l)).re = c * (l * Real.exp l) := by
    rw [← Complex.ofReal_exp]; norm_cast
  have h3 : ((c : ℂ) * ((l : ℂ) * Complex.exp (-l))).re = c * (l * Real.exp (-l)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]; norm_cast
  rw [h1, h2, h3]
  have hs : l * l ≤ l * Real.sinh l := by
    rcases le_total 0 l with h | h
    · exact mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.2 h) h
    · have : Real.sinh l ≤ l := by
        have := Real.self_le_sinh_iff.2 (neg_nonneg.2 h); rw [Real.sinh_neg] at this; linarith
      nlinarith
  rw [Real.sinh_eq] at hs
  nlinarith

theorem two_re_le (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    2 * (trace (prP ε * pB ε B * pB ε B)).re ≤
      (trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) - trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B))).re := by
  have hX := pB_isHermitian ε B
  set U : Matrix (Fin n) (Fin n) ℂ := (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self hX.eigenvectorUnitary
  set l : Fin n → ℝ := hX.eigenvalues
  set d : Fin n → ℂ := fun i => (l i : ℂ) with hd
  have hdec : pB ε B = U * diagonal d * star U := by
    have := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hunit : IsUnit U := ⟨⟨U, star U, hU', hU⟩, rfl⟩
  have hinv : U⁻¹ = star U := inv_eq_left_inv hU
  have hexp : ∀ w : Fin n → ℂ, NormedSpace.exp (U * diagonal w * star U) =
      U * diagonal (fun i => Complex.exp (w i)) * star U := by
    intro w
    rw [← hinv, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  have hdn : diagonal (fun i => -d i) = -diagonal d := by
    ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
  have hneg : -pB ε B = U * diagonal (fun i => -d i) * star U := by
    rw [hdec, hdn, Matrix.mul_neg, Matrix.neg_mul]
  have hmul : ∀ v w : Fin n → ℂ, (U * diagonal v * star U) * (U * diagonal w * star U) =
      U * diagonal (fun i => v i * w i) * star U := by
    intro v w
    calc (U * diagonal v * star U) * (U * diagonal w * star U) = U * diagonal v * (star U * U) * diagonal w * star U := by
          simp only [mul_assoc]
      _ = _ := by rw [hU, mul_one, mul_assoc U, diagonal_mul_diagonal]
  have hE : NormedSpace.exp (pB ε B) = U * diagonal (fun i => Complex.exp (d i)) * star U := by rw [hdec]; exact hexp d
  have hE' : NormedSpace.exp (-pB ε B) = U * diagonal (fun i => Complex.exp (-d i)) * star U := by
    rw [hneg]; exact hexp _
  have t0 : trace (prP ε * pB ε B * pB ε B) = ∑ i, (star U * prP ε * U) i i * (d i * d i) := by
    rw [mul_assoc, hdec, hmul, trace_conj_diag _ hU]
  have t1 : trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) =
      ∑ i, (star U * prP ε * U) i i * (d i * Complex.exp (d i)) := by
    rw [mul_assoc, hE, hdec, hmul, trace_conj_diag _ hU]
  have t2 : trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B)) =
      ∑ i, (star U * prP ε * U) i i * (d i * Complex.exp (-d i)) := by
    rw [mul_assoc, hE', hdec, hmul, trace_conj_diag _ hU]
  rw [t0, t1, t2, Complex.re_sum, Finset.mul_sum, Complex.sub_re, Complex.re_sum, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨c, hc, hci⟩ := conjDiag_re_nonneg U ε i
  rw [hci]
  exact re_term c (l i) hc

theorem le_of_le_sqrt_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ Real.sqrt a * Real.sqrt b) : a ≤ b := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · rw [← h0]; exact hb
  · have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 h0
    have h1 : Real.sqrt a * Real.sqrt a ≤ Real.sqrt a * Real.sqrt b := by rwa [Real.mul_self_sqrt ha]
    have h2 : Real.sqrt a ≤ Real.sqrt b := le_of_mul_le_mul_left h1 hs
    have := mul_le_mul h2 h2 (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    rwa [Real.mul_self_sqrt ha, Real.mul_self_sqrt hb] at this

theorem stExpLow : StExpLow := by
  intro n ε B
  set E : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp (pB ε B) with hEdef
  have hH : E.IsHermitian := (pB_isHermitian ε B).exp
  set T := trace (prP ε * pB ε B * E)
  have h2 := two_re_le ε B
  rw [trace_neg_side, trace_projection_mul_modeMatrix_mul_self, Complex.ofReal_re] at h2
  have hT : (∑ x, ‖B x‖ ^ 2) ≤ T.re := by
    have : (T - -T).re = 2 * T.re := by simp [Complex.sub_re, Complex.neg_re]; ring
    rw [this] at h2; linarith
  have hTn : ‖T‖ ≤ ∑ x : Mode ε, ‖B x‖ * ‖E x.1.1 x.1.2‖ := by
    rw [show T = ∑ x : Mode ε, B x * E x.1.2 x.1.1 from trace_projection_mul_modeMatrix_mul ε B E]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, ← hH.apply x.1.1 x.1.2, norm_star]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun x : Mode ε => ‖B x‖) (fun x : Mode ε => ‖E x.1.1 x.1.2‖)
  have hr : rM ε E = ∑ x : Mode ε, ‖E x.1.1 x.1.2‖ ^ 2 := rfl
  rw [hr]
  exact le_of_le_sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
    (hT.trans ((Complex.re_le_norm T).trans (hTn.trans hcs)))

end GlobalTheory.PsCo.Pc3
