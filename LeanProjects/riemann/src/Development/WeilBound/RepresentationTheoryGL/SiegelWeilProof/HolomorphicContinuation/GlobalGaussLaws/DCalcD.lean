import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcC
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.PowMulExpLeHalfExp

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcDH

open DCalcH DCalcBH

variable {m n : ℕ}

def sqN (v : Fin m → Fin n → ℂ) : ℝ := ∑ a, ∑ j, ‖v a j‖ ^ 2

theorem sqN_nonneg (v : Fin m → Fin n → ℂ) : 0 ≤ sqN v := by
  unfold sqN; positivity

theorem norm_le_one_add_sq (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ‖v a j‖ ≤ 1 + sqN v := by
  have h1 : ‖v a j‖ ^ 2 ≤ sqN v := by
    unfold sqN
    have ha : ‖v a j‖ ^ 2 ≤ ∑ j', ‖v a j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun j' => ‖v a j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    exact ha.trans (Finset.single_le_sum (f := fun a' => ∑ j', ‖v a' j'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ a))
  nlinarith [norm_nonneg (v a j), sq_nonneg (‖v a j‖ - 1)]

theorem norm_crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ‖crd v k‖ = ‖v k.1 k.2.1‖ := by
  unfold crd; split_ifs <;> simp

theorem evX_growth (Q : PX m n) : ∃ C N, 0 ≤ C ∧ ∀ v, ‖evX Q v‖ ≤ C * (1 + sqN v) ^ N := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun v => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨C1, N1, hC1, h1⟩ := hp
    obtain ⟨C2, N2, hC2, h2⟩ := hq
    refine ⟨C1 + C2, max N1 N2, by positivity, fun v => ?_⟩
    have hs : 1 ≤ 1 + sqN v := by linarith [sqN_nonneg v]
    have e1 := pow_le_pow_right₀ hs (le_max_left N1 N2)
    have e2 := pow_le_pow_right₀ hs (le_max_right N1 N2)
    calc ‖evX (p + q) v‖ ≤ ‖evX p v‖ + ‖evX q v‖ := by rw [evX_eq, map_add]; exact norm_add_le _ _
      _ ≤ C1 * (1 + sqN v) ^ N1 + C2 * (1 + sqN v) ^ N2 := add_le_add (h1 v) (h2 v)
      _ ≤ C1 * (1 + sqN v) ^ max N1 N2 + C2 * (1 + sqN v) ^ max N1 N2 :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
      _ = (C1 + C2) * (1 + sqN v) ^ max N1 N2 := by ring
  | mul_X p k hp =>
    obtain ⟨C, N, hC, h⟩ := hp
    refine ⟨C, N + 1, hC, fun v => ?_⟩
    have hk : ‖crd v k‖ ≤ 1 + sqN v := by rw [norm_crd]; exact norm_le_one_add_sq v _ _
    calc ‖evX (p * X k) v‖ = ‖evX p v‖ * ‖crd v k‖ := by rw [evX_eq, map_mul, eval_X, norm_mul]; rfl
      _ ≤ C * (1 + sqN v) ^ N * (1 + sqN v) :=
          mul_le_mul (h v) hk (norm_nonneg _) (mul_nonneg hC (pow_nonneg (by linarith [sqN_nonneg v]) _))
      _ = C * (1 + sqN v) ^ (N + 1) := by ring

theorem poly_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) :=
  _root_.UpperTheory.Reformulated.B.P6.r23b.PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp N a ha

theorem integrable_gauss_C (a : ℝ) (ha : 0 < a) : Integrable (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (a : ℂ)) (by simpa using ha) 0 0
  refine h.norm.congr (Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, ← Complex.ofReal_pow]

theorem integrable_gauss (a : ℝ) (ha : 0 < a) : Integrable (fun u : Fin m → Fin n → ℂ => Real.exp (-(a * sqN u))) := by
  have hinner : Integrable (fun w : Fin n → ℂ => ∏ j, Real.exp (-(a * ‖w j‖ ^ 2))) :=
    Integrable.fintype_prod (ι := Fin n) (E := ℂ) (μ := fun _ => (volume : Measure ℂ))
      (f := fun _ z => Real.exp (-(a * ‖z‖ ^ 2))) fun _ => integrable_gauss_C a ha
  have houter : Integrable (fun u : Fin m → Fin n → ℂ => ∏ i, ∏ j, Real.exp (-(a * ‖u i j‖ ^ 2))) :=
    Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ)))
      (f := fun _ w => ∏ j, Real.exp (-(a * ‖w j‖ ^ 2))) fun _ => hinner
  refine houter.congr (Eventually.of_forall fun u => ?_)
  simp only [sqN]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

end DCalcDH

end PositivityTheory.Rg.Sw.Glob
