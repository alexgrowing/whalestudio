import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.IntgPowQuad

noncomputable section

open scoped FourierTransform
open MeasureTheory Complex MvPolynomial

namespace PositivityTheory.SiegelWeilFormula.KFPB

open PositivityTheory.SiegelWeilFormula.KLI (J pk J_eq J_zero intg_pow_quad pk_deg)

variable {ι : Type} [Fintype ι]

theorem integral_euc (g : EuclideanSpace ℝ ι → ℂ) :
    ∫ η, g η = ∫ x : ι → ℝ, g (WithLp.toLp 2 x) := by
  have h := (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding g
  rw [← h]

theorem integrable_euc {g : EuclideanSpace ℝ ι → ℂ} (hg : Integrable (fun x : ι → ℝ => g (WithLp.toLp 2 x))) :
    Integrable g := by
  have h := (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding (g := g)
  exact h.1 hg

theorem norm_sq_euc (x : EuclideanSpace ℝ ι) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp

theorem inner_euc (x y : EuclideanSpace ℝ ι) : inner ℝ x y = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

def phi (b : ℝ) (k : ℕ) (c : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ k * cexp ((-b : ℂ) * (x : ℂ) ^ 2 + c * x)

theorem integrable_phi {b : ℝ} (hb : 0 < b) (k : ℕ) (c : ℂ) : Integrable (phi b k c) := by
  have h : ((-b : ℂ)).re < 0 := by simp; linarith
  exact intg_pow_quad h k c

theorem integral_phi {b : ℝ} (hb : 0 < b) (k : ℕ) (c : ℂ) :
    ∫ x, phi b k c x = (pk (-b : ℂ) k).eval c * (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * cexp (c ^ 2 / (4 * b))) := by
  have h : ((-b : ℂ)).re < 0 := by simp; linarith
  have e1 := J_eq h k c
  rw [J_zero h] at e1
  have e2 : ∫ x, phi b k c x = J (-b : ℂ) k c := rfl
  rw [e2, e1]
  congr 2
  · rw [neg_neg]
  · congr 1; ring

theorem circle_smul (r : ℝ) (z : ℂ) : (𝐞 r) • z = cexp (2 * Real.pi * r * I) * z := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  push_cast
  ring_nf

theorem eval_mono (s : ι →₀ ℕ) (y : ι → ℂ) : eval y (monomial s (1 : ℂ)) = ∏ i, y i ^ s i := by
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (by simp)]

theorem mono_prod (b : ℝ) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) (x : ι → ℝ) :
    𝐞 (inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) u) •
      (eval (fun i => (((WithLp.toLp 2 x : EuclideanSpace ℝ ι) i : ℝ) : ℂ)) (monomial s (1 : ℂ)) *
        (Real.exp (-(b * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2)) : ℂ)) =
      ∏ i, phi b (s i) (2 * Real.pi * I * u i) (x i) := by
  rw [circle_smul, eval_mono, inner_euc, norm_sq_euc]
  simp only [phi, Finset.prod_mul_distrib, ← Complex.exp_sum]
  rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem integrable_mono {b : ℝ} (hb : 0 < b) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) :
    Integrable (fun η : EuclideanSpace ℝ ι => 𝐞 (inner ℝ η u) •
      (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ))) := by
  refine integrable_euc ?_
  simp_rw [mono_prod]
  exact Integrable.fintype_prod (f := fun i y => phi b (s i) (2 * Real.pi * I * u i) y)
    fun i => integrable_phi hb _ _

theorem integral_mono {b : ℝ} (hb : 0 < b) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) :
    ∫ η : EuclideanSpace ℝ ι, 𝐞 (inner ℝ η u) •
      (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) =
      ∏ i, ((pk (-b : ℂ) (s i)).eval (2 * Real.pi * I * u i) *
        (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * cexp ((2 * Real.pi * I * u i) ^ 2 / (4 * b)))) := by
  rw [integral_euc]
  simp_rw [mono_prod]
  rw [integral_fintype_prod_volume_eq_prod (f := fun i y => phi b (s i) (2 * Real.pi * I * u i) y)]
  simp_rw [integral_phi hb]

def kG (b : ℝ) : ℂ := ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ)

theorem prod_gauss {b : ℝ} (hb : 0 < b) (u : EuclideanSpace ℝ ι) (A : ι → ℂ) :
    ∏ i, (A i * (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * cexp ((2 * Real.pi * I * u i) ^ 2 / (4 * b)))) =
      (∏ i, A i) * kG b ^ Fintype.card ι * (Real.exp (-(Real.pi ^ 2 / b * ‖u‖ ^ 2)) : ℂ) := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← Complex.exp_sum, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, norm_sq_euc]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring_nf
  rw [I_sq]
  ring

def linP (i : ι) (a : ℂ) (p : Polynomial ℂ) : MvPolynomial ι ℂ :=
  ∑ j ∈ Finset.range (p.natDegree + 1), C (p.coeff j * a ^ j) * X i ^ j

omit [Fintype ι] in
theorem eval_linP (i : ι) (a : ℂ) (p : Polynomial ℂ) (g : ι → ℂ) : eval g (linP i a p) = p.eval (a * g i) := by
  rw [Polynomial.eval_eq_sum_range, linP, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_pow, mul_assoc]

omit [Fintype ι] in
theorem deg_linP (i : ι) (a : ℂ) (p : Polynomial ℂ) : (linP i a p).totalDegree ≤ p.natDegree := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_pow _ _).trans ?_
  have := Finset.mem_range.mp hj
  have h1 : (X i : MvPolynomial ι ℂ).totalDegree ≤ 1 := by rw [totalDegree_X]
  nlinarith

def rS (b : ℝ) (s : ι →₀ ℕ) : MvPolynomial ι ℂ :=
  C (kG b ^ Fintype.card ι) * ∏ i, linP i (2 * Real.pi * I) (pk (-b : ℂ) (s i))

theorem eval_rS (b : ℝ) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) :
    eval (fun i => ((u i : ℝ) : ℂ)) (rS b s) =
      kG b ^ Fintype.card ι * ∏ i, (pk (-b : ℂ) (s i)).eval (2 * Real.pi * I * u i) := by
  simp [rS, eval_linP]

theorem deg_rS (b : ℝ) (s : ι →₀ ℕ) : (rS b s).totalDegree ≤ s.sum (fun _ e => e) := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_le_sum fun i _ => (deg_linP _ _ _).trans (pk_deg _ _)

theorem integral_mono' {b : ℝ} (hb : 0 < b) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) :
    ∫ η : EuclideanSpace ℝ ι, 𝐞 (inner ℝ η u) •
      (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) =
      eval (fun i => ((u i : ℝ) : ℂ)) (rS b s) * (Real.exp (-(Real.pi ^ 2 / b * ‖u‖ ^ 2)) : ℂ) := by
  rw [integral_mono hb, prod_gauss hb, eval_rS]
  ring

omit [Fintype ι] in
theorem eval_as_sum (Q : MvPolynomial ι ℂ) (y : ι → ℂ) :
    eval y Q = ∑ s ∈ Q.support, coeff s Q * eval y (monomial s (1 : ℂ)) := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [eval_monomial, eval_monomial, one_mul]

theorem e_zero (η : EuclideanSpace ℝ ι) (z : ℂ) : 𝐞 (inner ℝ η (0 : EuclideanSpace ℝ ι)) • z = z := by
  rw [circle_smul, inner_zero_right]
  simp

theorem integrable_mono0 {b : ℝ} (hb : 0 < b) (s : ι →₀ ℕ) :
    Integrable (fun η : EuclideanSpace ℝ ι =>
      eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) := by
  have h := integrable_mono hb s 0
  simp_rw [e_zero] at h
  exact h

theorem integrable_poly_gauss {ι : Type} [Fintype ι] (b : ℝ) (hb : 0 < b) (Q : MvPolynomial ι ℂ) :
    MeasureTheory.Integrable (fun η : EuclideanSpace ℝ ι =>
      MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) := by
  have e : (fun η : EuclideanSpace ℝ ι =>
      MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) = fun η =>
      ∑ s ∈ Q.support, coeff s Q *
        (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) := by
    funext η
    rw [eval_as_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun s _ => (integrable_mono0 hb s).const_mul _

theorem fourierInv_poly_gauss {ι : Type} [Fintype ι] (b : ℝ) (hb : 0 < b) (Q : MvPolynomial ι ℂ) :
    ∃ Q' : MvPolynomial ι ℂ, Q'.totalDegree ≤ Q.totalDegree ∧ ∀ u : EuclideanSpace ℝ ι,
      𝓕⁻ (fun η : EuclideanSpace ℝ ι =>
          MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) u =
        MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) Q' * (Real.exp (-(Real.pi ^ 2 / b * ‖u‖ ^ 2)) : ℂ) := by
  refine ⟨∑ s ∈ Q.support, C (coeff s Q) * rS b s, ?_, fun u => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (deg_rS b s).trans (le_totalDegree hs)
  · rw [Real.fourierInv_eq]
    have e : ∀ η : EuclideanSpace ℝ ι, 𝐞 (inner ℝ η u) •
        (eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) =
        ∑ s ∈ Q.support, coeff s Q * (𝐞 (inner ℝ η u) •
          (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ))) := by
      intro η
      rw [eval_as_sum, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [circle_smul, circle_smul]
      ring
    simp_rw [e]
    rw [integral_finsetSum _ fun s _ => (integrable_mono hb s u).const_mul _]
    simp_rw [integral_const_mul, integral_mono' hb]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eval_mul, eval_C]
    ring

end PositivityTheory.SiegelWeilFormula.KFPB

end
