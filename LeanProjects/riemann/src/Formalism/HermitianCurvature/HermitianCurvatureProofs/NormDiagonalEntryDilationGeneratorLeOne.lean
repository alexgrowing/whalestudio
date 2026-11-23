import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralZeroFrequencyInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B6

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def X0 (k r : ℕ) : Mat k r := Matrix.diagonal fun i =>
  if i.val < r then ((((r - i.val : ℕ) : ℝ) / ((r : ℝ) + 1) : ℝ) : ℂ)
  else if i.val ≤ r + k then 0 else ((-(((i.val - (r + k) : ℕ) : ℝ) / ((r : ℝ) + 1)) : ℝ) : ℂ)

def rr (r : ℕ) : ℝ := (r : ℝ) + 1

section spaces

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def admitted (α c : ℝ) (f : Mat k r → E) : Prop :=
  ContinuousOn f (GV k r) ∧ ∀ g ∈ GV k r, gN g ^ α * ‖f g‖ ≤ c

def DR (f : Mat k r → E) : Prop :=
  ∀ g ∈ GV k r, HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X0 k r))) (RdV (X0 k r) f g) 0

def DL (f : Mat k r → E) : Prop :=
  ∀ g ∈ GV k r, HasDerivAt (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X0 k r)) * g)) (LdV (X0 k r) f g) 0

abbrev Rr (f : Mat k r → E) : Mat k r → E := RdV (X0 k r) f

abbrev Ll (f : Mat k r → E) : Mat k r → E := LdV (X0 k r) f

def AdmW (α c : ℝ) (n m : ℕ) (f : Mat k r → E) : Prop :=
  (∀ j ≤ n, ∀ i ≤ m, admitted α c (Ll^[i] (Rr^[j] f))) ∧ (∀ j < n, DR (Rr^[j] f)) ∧
    ∀ j ≤ n, ∀ i < m, DL (Ll^[i] (Rr^[j] f))

end spaces

def gam (ρ : ℝ) (W : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => W t - iteratedDeriv 2 W t
  | 1 => fun t => 2 * ρ * deriv W t / t - ρ * W t / t ^ 2
  | _ => fun t => -(ρ ^ 2 * W t / t ^ 2)

section setting

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def Wd (D : RealPlaceData k r Wp Wq) (t : ℝ) : ℝ := D.χ t * t ^ kap k r

def QL (D : RealPlaceData k r Wp Wq) (p : SS k r) :
    ℕ → (Mat k r → (Wq →L[ℂ] Wp)) → (Mat k r → (Wq →L[ℂ] Wp)) → ℝ → ℝ → ℂ
  | 0, A, B => fun x y => Ph D A B (dilation₂ (x, y) p)
  | m + 1, A, B => fun x y => QL D p m (Ll A) B x y + QL D p m A (Ll B) x y

def QR (D : RealPlaceData k r Wp Wq) (p : SS k r) (m : ℕ) :
    ℕ → (Mat k r → (Wq →L[ℂ] Wp)) → (Mat k r → (Wq →L[ℂ] Wp)) → ℝ → ℝ → ℂ
  | 0, A, B => QL D p m A B
  | l + 1, A, B => fun x y => QR D p m l (Rr A) B x y + QR D p m l A (Rr B) x y

structure Hyp (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (α : ℝ) : Prop where
  α_nonneg : 0 ≤ α
  coef : CoefBound D Ξ α
  xi : XiInt D Ξ 2
  T0 : ∃ T : Wq →L[ℂ] Wp, ‖T‖ = 1
  dilN : DilN
  dilUW : DilUW

def XX (Ξ : Mat k r → NNReal) (p : SS k r) : ℝ :=
  (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) : ℝ) * (Ξ (Matrix.of p.2.2 * Matrix.of p.2.1) : ℝ)

def Ef (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (t : ℝ × ℝ) : ℂ :=
  ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
    ((gam (rr r) (Wd D) m t.1 * gam (rr r) (Wd D) l t.2 : ℝ) : ℂ) * QR D p m l F F' t.1 t.2

end setting

section basic

variable {k r : ℕ}

theorem rr_pos (r : ℕ) : 0 < rr r := by unfold rr; positivity

def dilationGeneratorDiagonal (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then ((((r - i.val : ℕ) : ℝ) / ((r : ℝ) + 1) : ℝ) : ℂ)
  else if i.val ≤ r + k then 0 else ((-(((i.val - (r + k) : ℕ) : ℝ) / ((r : ℝ) + 1)) : ℝ) : ℂ)

theorem lie_element_eq_diagonal (k r : ℕ) : X0 k r = Matrix.diagonal (dilationGeneratorDiagonal k r) := rfl

theorem hermitian_entry_zero_or_weights_cancel (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = 0 ∨ dilationGeneratorDiagonal k r i + dilationGeneratorDiagonal k r j = 0 := by
  by_cases c1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · right
    have h1 : ¬ j.val < r := by omega
    have h2 : ¬ j.val ≤ r + k := by omega
    have h3 : j.val - (r + k) = r - i.val := by omega
    simp only [dilationGeneratorDiagonal, c1.1, h1, h2, if_true, if_false, h3]
    push_cast; ring
  · by_cases c2 : j.val < r ∧ i.val + j.val = 2 * r + k
    · right
      have h1 : ¬ i.val < r := by omega
      have h2 : ¬ i.val ≤ r + k := by omega
      have h3 : i.val - (r + k) = r - j.val := by omega
      simp only [dilationGeneratorDiagonal, c2.1, h1, h2, if_true, if_false, h3]
      push_cast; ring
    · by_cases c3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
      · right
        obtain ⟨a, b, rfl⟩ := c3
        have h1 : ¬ i.val < r := by omega
        simp [dilationGeneratorDiagonal, h1, b]
      · left
        simp [Hpk, c1, c2, c3]

theorem diagonal_lie_element_self_adjoint (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (dilationGeneratorDiagonal k r i) = dilationGeneratorDiagonal k r i := by
  unfold dilationGeneratorDiagonal
  split_ifs <;> simp

theorem norm_diagonal_entry_dilation_generator_le_one (k r : ℕ) (i : Fin (2 * r + k + 1)) : ‖dilationGeneratorDiagonal k r i‖ ≤ 1 := by
  unfold dilationGeneratorDiagonal
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  split_ifs with h1 h2
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one hr]
    have : ((r - i.val : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le _ _
    linarith
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity), div_le_one hr]
    have h3 : i.val - (r + k) ≤ r := by have := i.isLt; omega
    have : ((i.val - (r + k) : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h3
    linarith

theorem lie_element_unitary (k r : ℕ) : unitLie k r (X0 k r) := by
  constructor
  · unfold inLie
    rw [lie_element_eq_diagonal, Matrix.diagonal_conjTranspose]
    ext i j
    rw [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply, Pi.star_apply, diagonal_lie_element_self_adjoint]
    rcases hermitian_entry_zero_or_weights_cancel k r i j with h | h
    · rw [h]; ring
    · linear_combination (Hpk k r i j) * h
  · intro i j
    rw [lie_element_eq_diagonal, Matrix.diagonal_apply]
    split_ifs with h
    · exact norm_diagonal_entry_dilation_generator_le_one k r i
    · simp

theorem exp_dilation_generator_eq_aDil (k r : ℕ) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X0 k r) = aDil k r (Real.exp (s / rr r)) := by
  rw [lie_element_eq_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  unfold aDil
  congr 1
  funext i
  rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  have hr : (rr r) ≠ 0 := (rr_pos r).ne'
  unfold dilationGeneratorDiagonal
  split_ifs with h1 h2
  · rw [← Real.exp_nat_mul, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    unfold rr; field_simp
  · simp
  · rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    unfold rr; field_simp

theorem aDil_mem (k r : ℕ) {t : ℝ} (ht : 0 < t) : aDil k r t ∈ GV k r := dilation_mem_group k r t ht.ne'

theorem aDil_inv_mem (k r : ℕ) {t : ℝ} (ht : 0 < t) : (aDil k r t)⁻¹ ∈ GV k r :=
  WeylGroupFacts.uh_inv (aDil_mem k r ht)

theorem exp_mem (k r : ℕ) (s : ℝ) : NormedSpace.exp ((s : ℂ) • X0 k r) ∈ GV k r := by
  rw [exp_dilation_generator_eq_aDil]; exact aDil_mem k r (Real.exp_pos _)

theorem exp_neg_dilation_generator_eq_aDil (k r : ℕ) (s : ℝ) :
    NormedSpace.exp (-((s : ℂ) • X0 k r)) = aDil k r (Real.exp (-s / rr r)) := by
  rw [← exp_dilation_generator_eq_aDil, ← neg_smul, Complex.ofReal_neg]

theorem exp_neg_mem (k r : ℕ) (s : ℝ) : NormedSpace.exp (-((s : ℂ) • X0 k r)) ∈ GV k r := by
  rw [exp_neg_dilation_generator_eq_aDil]; exact aDil_mem k r (Real.exp_pos _)

theorem aDil_one (k r : ℕ) : aDil k r 1 = 1 := by
  unfold aDil
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem aDil_mul_eq_mul_aDil (k r : ℕ) (t t' : ℝ) : aDil k r (t * t') = aDil k r t * aDil k r t' := by
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs
  · rw [mul_pow]; push_cast; ring
  · simp
  · rw [mul_pow, mul_inv]; push_cast; ring

theorem hasDerivAt_curveR (g : Mat k r) :
    HasDerivAt (fun s : ℝ => g * NormedSpace.exp ((s : ℂ) • X0 k r)) (g * X0 k r) 0 :=
  hasDerivAt_mul_exp_smul_zero g (X0 k r)

theorem hasDerivAt_curveL (g : Mat k r) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (-((s : ℂ) • X0 k r)) * g) (-(X0 k r * g)) 0 := by
  have h := (tendsto_slope_exp_smul (-(X0 k r))).mul_const g
  rw [Matrix.neg_mul] at h
  refine hasDerivAt_iff_tendsto_slope.mpr (h.congr (fun t => ?_))
  simp only [slope_def_module, Matrix.sub_mul, Matrix.smul_mul, smul_neg]

theorem hasDerivAt_log_difference_scaled (r : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => rr r * (Real.log y - Real.log y')) (-(rr r / y)) y := by
  have h := ((Real.hasDerivAt_log hy.ne').const_sub (Real.log y)).const_mul (rr r)
  have e : rr r * -y⁻¹ = -(rr r / y) := by rw [div_eq_mul_inv]; ring
  rw [e] at h
  exact h

theorem exp_log_ratio (r : ℕ) {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    Real.exp (rr r * (Real.log y - Real.log y') / rr r) = y / y' := by
  rw [mul_div_cancel_left₀ _ (rr_pos r).ne', Real.exp_sub, Real.exp_log hy, Real.exp_log hy']

theorem curveR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Mat k r → E) (z : Mat k r) {y : ℝ}
    (hy : 0 < y) {d : E}
    (h : HasDerivAt (fun s : ℝ => f (z * (aDil k r y)⁻¹ * NormedSpace.exp ((s : ℂ) • X0 k r))) d 0) :
    HasDerivAt (fun y' : ℝ => f (z * (aDil k r y')⁻¹)) ((-(rr r / y)) • d) y := by
  have h0 : rr r * (Real.log y - Real.log y) = 0 := by simp
  have hc := HasDerivAt.scomp_of_eq y h (hasDerivAt_log_difference_scaled r hy) h0.symm
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hy] with y' hy'
  simp only [Function.comp]
  rw [exp_dilation_generator_eq_aDil, exp_log_ratio r hy hy', B2.aDil_inv k r y hy.ne', B2.aDil_inv k r y' hy'.ne', Matrix.mul_assoc,
    ← aDil_mul_eq_mul_aDil]
  congr 3
  field_simp

theorem curveL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Mat k r → E) (z : Mat k r) {x : ℝ}
    (hx : 0 < x) {d : E}
    (h : HasDerivAt (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X0 k r)) * (aDil k r x * z))) d 0) :
    HasDerivAt (fun x' : ℝ => f (aDil k r x' * z)) ((-(rr r / x)) • d) x := by
  have h0 : rr r * (Real.log x - Real.log x) = 0 := by simp
  have hc := HasDerivAt.scomp_of_eq x h (hasDerivAt_log_difference_scaled r hx) h0.symm
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with x' hx'
  simp only [Function.comp]
  have e : Real.exp (-(rr r * (Real.log x - Real.log x')) / rr r) = x' / x := by
    rw [show -(rr r * (Real.log x - Real.log x')) = rr r * (Real.log x' - Real.log x) by ring]
    exact exp_log_ratio r hx' hx
  rw [exp_neg_dilation_generator_eq_aDil, e, ← Matrix.mul_assoc, ← aDil_mul_eq_mul_aDil]
  congr 3
  field_simp

theorem gN_nonneg (g : Mat k r) : 0 ≤ gN g := Real.sqrt_nonneg _

def hilbertSchmidtNormSq (g : Mat k r) : ℝ := ∑ i, ∑ j, Complex.normSq (g i j)

theorem sum_normSq_entries_nonneg (g : Mat k r) : 0 ≤ hilbertSchmidtNormSq g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem matrix_product_entry_bound (a b : Mat k r) (i j : Fin (2 * r + k + 1)) :
    Complex.normSq ((a * b) i j) ≤ (∑ l, Complex.normSq (a i l)) * ∑ l, Complex.normSq (b l j) := by
  rw [Matrix.mul_apply, Complex.normSq_eq_norm_sq]
  have h1 : ‖∑ l, a i l * b l j‖ ≤ ∑ l, ‖a i l‖ * ‖b l j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun l _ => norm_mul _ _
  have h2 : (∑ l, ‖a i l‖ * ‖b l j‖) ^ 2 ≤ (∑ l, ‖a i l‖ ^ 2) * ∑ l, ‖b l j‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖∑ l, a i l * b l j‖ ^ 2 ≤ (∑ l, ‖a i l‖ * ‖b l j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ l, ‖a i l‖ ^ 2) * ∑ l, ‖b l j‖ ^ 2 := h2
    _ = _ := by simp only [Complex.normSq_eq_norm_sq]

theorem sum_normSq_entries_mul_le (a b : Mat k r) : hilbertSchmidtNormSq (a * b) ≤ hilbertSchmidtNormSq a * hilbertSchmidtNormSq b := by
  unfold hilbertSchmidtNormSq
  calc ∑ i, ∑ j, Complex.normSq ((a * b) i j)
      ≤ ∑ i, ∑ j, (∑ l, Complex.normSq (a i l)) * ∑ l, Complex.normSq (b l j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => matrix_product_entry_bound a b i j
    _ = (∑ i, ∑ l, Complex.normSq (a i l)) * ∑ j, ∑ l, Complex.normSq (b l j) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ l, Complex.normSq (a i l)) * ∑ l, ∑ j, Complex.normSq (b l j) := by
        rw [Finset.sum_comm (f := fun j l => Complex.normSq (b l j))]

theorem gN_mul_le (a b : Mat k r) : gN (a * b) ≤ gN a * gN b := by
  have h : gN a * gN b = Real.sqrt (hilbertSchmidtNormSq a * hilbertSchmidtNormSq b) := (Real.sqrt_mul (sum_normSq_entries_nonneg a) _).symm
  rw [h]
  exact Real.sqrt_le_sqrt (sum_normSq_entries_mul_le a b)

theorem gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := by
  apply Real.sqrt_pos.2
  by_contra hcon
  have h0 : hilbertSchmidtNormSq g = 0 := le_antisymm (not_lt.1 hcon) (sum_normSq_entries_nonneg g)
  have hz : g = 0 := by
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (g i j))).1 h0 i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (g i j))).1 h1 j (Finset.mem_univ _)
    simpa using Complex.normSq_eq_zero.1 h2
  have hu := WeylGroupFacts.isUnit_of_uh hg
  rw [hz, Matrix.det_zero] at hu
  exact not_isUnit_zero hu

theorem gN_continuous : Continuous (gN : Mat k r → ℝ) := by
  unfold gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp (continuous_id.matrix_elem i j)

theorem aDil_continuousOn (k r : ℕ) : ContinuousOn (fun t : ℝ => aDil k r t) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  unfold aDil
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  show Continuous fun t : Set.Ioi (0 : ℝ) => if i.val < r then (((t : ℝ) ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else ((((t : ℝ) ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)
  split_ifs
  · exact Complex.continuous_ofReal.comp (continuous_subtype_val.pow _)
  · exact continuous_const
  · refine Complex.continuous_ofReal.comp (Continuous.inv₀ (continuous_subtype_val.pow _) ?_)
    intro t
    exact pow_ne_zero _ (ne_of_gt t.2)

theorem aDil_inv_continuousOn (k r : ℕ) : ContinuousOn (fun t : ℝ => (aDil k r t)⁻¹) (Set.Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => aDil k r t⁻¹) (Set.Ioi 0) := by
    refine (aDil_continuousOn k r).comp (continuousOn_inv₀.mono ?_) ?_
    · intro t ht; exact ne_of_gt ht
    · intro t ht; exact inv_pos.2 (Set.mem_Ioi.1 ht)
  refine h.congr ?_
  intro t ht
  exact B2.aDil_inv k r t (ne_of_gt ht)

theorem aDil_gN_bound (k r : ℕ) {a b : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc a b, gN (aDil k r t) ≤ K ∧ gN (aDil k r t)⁻¹ ≤ K := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le ha ht.1
  obtain ⟨C₁, h₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((gN_continuous.comp_continuousOn (aDil_continuousOn k r)).mono hsub)
  obtain ⟨C₂, h₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((gN_continuous.comp_continuousOn (aDil_inv_continuousOn k r)).mono hsub)
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun t ht => ⟨?_, ?_⟩⟩
  · exact ((le_abs_self _).trans (h₁ t ht)).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact ((le_abs_self _).trans (h₂ t ht)).trans ((le_max_right _ _).trans (le_max_left _ _))

end basic

section basic

variable {k r : ℕ}

theorem isClosed_GV (k r : ℕ) : IsClosed (GV k r) := by
  have h : Continuous fun g : Mat k r => gᴴ * Hpk k r * g :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq h continuous_const

theorem isClosed_Nset (k r : ℕ) : IsClosed (Nset k r) := by
  unfold QuantumDeterminants.Nset
  refine IsClosed.and (isClosed_GV k r) (IsClosed.and ?_ ?_)
  · simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  · simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_id.matrix_elem _ _) continuous_const

theorem isClosed_UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  unfold UWset
  refine IsClosed.and (isClosed_GV k r) (IsClosed.and ?_ ?_)
  · simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => IsClosed.and ?_ ?_
    · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
    · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

theorem inv_eq_hermitian_form_conjTranspose {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', WeylGroupFacts.hpk_sq]

theorem inv_continuousOn (k r : ℕ) : ContinuousOn (fun g : Mat k r => g⁻¹) (GV k r) := by
  have h : Continuous fun g : Mat k r => Hpk k r * gᴴ * Hpk k r :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  exact h.continuousOn.congr fun g hg => inv_eq_hermitian_form_conjTranspose hg

theorem lam_continuous (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Continuous (fun n : Mat k r => lam k r z n) := by
  unfold lam ell
  refine Complex.continuous_re.comp (continuous_const.mul ?_)
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dif_pos]
    exact continuous_id.matrix_elem _ _
  · simp only [h, dif_neg, not_false_iff]
    have h2 : Continuous fun n : Mat k r => n *ᵥ z := continuous_id.matrix_mulVec continuous_const
    exact (continuous_apply (eI k r a)).comp h2

theorem Nset_sub (k r : ℕ) : Nset k r ⊆ GV k r := fun _ h => h.1

theorem UWset_sub (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : UWset k r z ⊆ GV k r := fun _ h => h.1

theorem haar_sigmaFinite {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem haar_ae {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, (Matrix.of g : Mat k r) ∈ U := by
  rw [ae_iff]; exact h.conc

theorem admissible_two_sided_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {f : Mat k r → E}
    (hα : 0 ≤ α) (hf : admitted α c f) {u v : Mat k r} (hu : u ∈ GV k r) (hv : v ∈ GV k r) :
    admitted α (c * (gN u⁻¹ * gN v⁻¹) ^ α) (fun g => f (u * g * v)) := by
  have hmaps : ∀ g ∈ GV k r, u * g * v ∈ GV k r := fun g hg => WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hu hg) hv
  refine ⟨?_, ?_⟩
  · have hc : Continuous fun g : Mat k r => u * g * v :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hf.1.comp hc.continuousOn hmaps
  · intro g hg
    have hw := hmaps g hg
    have huu := WeylGroupFacts.isUnit_of_uh hu
    have hvu := WeylGroupFacts.isUnit_of_uh hv
    have eg : g = u⁻¹ * (u * g * v) * v⁻¹ := by
      rw [Matrix.mul_assoc u g v, Matrix.nonsing_inv_mul_cancel_left _ _ huu, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hvu, Matrix.mul_one]
    have h1 : gN g ≤ (gN u⁻¹ * gN v⁻¹) * gN (u * g * v) := by
      calc gN g = gN (u⁻¹ * (u * g * v) * v⁻¹) := by rw [← eg]
        _ ≤ gN (u⁻¹ * (u * g * v)) * gN v⁻¹ := gN_mul_le _ _
        _ ≤ gN u⁻¹ * gN (u * g * v) * gN v⁻¹ :=
            mul_le_mul_of_nonneg_right (gN_mul_le _ _) (gN_nonneg _)
        _ = (gN u⁻¹ * gN v⁻¹) * gN (u * g * v) := by ring
    have hK : 0 ≤ gN u⁻¹ * gN v⁻¹ := mul_nonneg (gN_nonneg _) (gN_nonneg _)
    have h2 : gN g ^ α ≤ (gN u⁻¹ * gN v⁻¹) ^ α * gN (u * g * v) ^ α := by
      rw [← Real.mul_rpow hK (gN_nonneg _)]
      exact Real.rpow_le_rpow (gN_nonneg _) h1 hα
    calc gN g ^ α * ‖f (u * g * v)‖
        ≤ ((gN u⁻¹ * gN v⁻¹) ^ α * gN (u * g * v) ^ α) * ‖f (u * g * v)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = (gN u⁻¹ * gN v⁻¹) ^ α * (gN (u * g * v) ^ α * ‖f (u * g * v)‖) := by ring
      _ ≤ (gN u⁻¹ * gN v⁻¹) ^ α * c :=
          mul_le_mul_of_nonneg_left (hf.2 _ hw) (Real.rpow_nonneg hK _)
      _ = c * (gN u⁻¹ * gN v⁻¹) ^ α := by ring

theorem admissible_constant_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {f : Mat k r → E}
    (hf : admitted α c f) : 0 ≤ c :=
  le_trans (mul_nonneg (Real.rpow_nonneg (gN_nonneg _) _) (norm_nonneg _)) (hf.2 1 WeylGroupFacts.uh_one)

theorem admissible_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {f : Mat k r → E}
    (hf : admitted α c f) {g : Mat k r} (hg : g ∈ GV k r) : ‖f g‖ ≤ c * gN g ^ (-α) := by
  have hp : 0 < gN g ^ α := Real.rpow_pos_of_pos (gN_pos hg) _
  rw [Real.rpow_neg (gN_nonneg g), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
  exact hf.2 g hg

theorem admissible_ae_strongly_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {f : Mat k r → E}
    (hf : admitted α c f) {μ : Measure (Mt k r)} (h : IsHaarOn (GV k r) μ) :
    AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) μ := by
  have hcl : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GV k r} := isClosed_GV k r
  have hm : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ GV k r} := hcl.measurableSet
  have hc : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) {x : Mt k r | (Matrix.of x : Mat k r) ∈ GV k r} :=
    hf.1
  have h1 := hc.aestronglyMeasurable (μ := μ) hm
  have h2 : μ.restrict {x : Mt k r | (Matrix.of x : Mat k r) ∈ GV k r} = μ :=
    Measure.restrict_eq_self_of_ae_mem (haar_ae h)
  rwa [h2] at h1

end basic

section setting

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem sigmaFinite_μSS (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by
  have := haar_sigmaFinite D.haarW
  have := haar_sigmaFinite D.haarN
  have := haar_sigmaFinite D.haarW'
  unfold RealPlaceData.μSS
  infer_instance

theorem ae_inSS (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := haar_sigmaFinite D.haarW
  have := haar_sigmaFinite D.haarN
  have := haar_sigmaFinite D.haarW'
  have h1 : ∀ᵐ p ∂D.μSS, (Matrix.of p.1.1 : Mat k r) ∈ UWset k r D.z :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst).ae (haar_ae D.haarW)
  have h2 : ∀ᵐ p ∂D.μSS, (Matrix.of p.1.2 : Mat k r) ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst).ae (haar_ae D.haarN)
  have h3 : ∀ᵐ p ∂D.μSS, (Matrix.of p.2.1 : Mat k r) ∈ UWset k r D.z' :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd).ae (haar_ae D.haarW')
  have h4 : ∀ᵐ p ∂D.μSS, (Matrix.of p.2.2 : Mat k r) ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae (haar_ae D.haarN)
  filter_upwards [h1, h2, h3, h4] with p a b c d
  exact ⟨a, b, c, d⟩

theorem setting_support_closed (D : RealPlaceData k r Wp Wq) : IsClosed {p : SS k r | D.inSS p} := by
  have c1 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} := isClosed_UWset k r D.z
  have c2 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Nset k r} := isClosed_Nset k r
  have c3 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z'} := isClosed_UWset k r D.z'
  unfold RealPlaceData.inSS
  refine IsClosed.and (c1.preimage (continuous_fst.comp continuous_fst))
    (IsClosed.and (c2.preimage (continuous_snd.comp continuous_fst))
      (IsClosed.and (c3.preimage (continuous_fst.comp continuous_snd))
        (c2.preimage (continuous_snd.comp continuous_snd))))

theorem measurableSet_inSS (D : RealPlaceData k r Wp Wq) : MeasurableSet {p : SS k r | D.inSS p} :=
  (setting_support_closed D).measurableSet

theorem dil_inSS (hN : DilN) (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) : D.inSS (dilation₂ (x, y) p) :=
  ⟨hp.1, (hN k r D.z x hx.ne' D.z_mem _ hp.2.1).1, hp.2.2.1, (hN k r D.z y hy.ne' D.z_mem _ hp.2.2.2).1⟩

theorem continuousOn_conj_by_dilation (k r : ℕ) (φ : SS k r × (ℝ × ℝ) → Mt k r) (hφ : Continuous φ)
    (ψ : SS k r × (ℝ × ℝ) → ℝ) (hψ : Continuous ψ) (hpos : ∀ q ∈ (Set.univ : Set (SS k r)) ×ˢ Quad, 0 < ψ q) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => conjM (aDil k r (ψ q)) (φ q)) (Set.univ ×ˢ Quad) := by
  have h1 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => aDil k r (ψ q)) (Set.univ ×ˢ Quad) :=
    (aDil_continuousOn k r).comp hψ.continuousOn hpos
  have h2 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => (aDil k r (ψ q))⁻¹) (Set.univ ×ˢ Quad) :=
    (aDil_inv_continuousOn k r).comp hψ.continuousOn hpos
  have h3 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => (Matrix.of (φ q) : Mat k r)) (Set.univ ×ˢ Quad) :=
    hφ.continuousOn
  exact (h1.mul h3).mul h2

theorem dilationAction_continuousOn (k r : ℕ) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => dilation₂ q.2 q.1) (Set.univ ×ˢ Quad) := by
  unfold dilation₂
  refine ContinuousOn.prodMk (ContinuousOn.prodMk ?_ ?_) (ContinuousOn.prodMk ?_ ?_)
  · exact (continuous_fst.comp (continuous_fst.comp continuous_fst)).continuousOn
  · exact continuousOn_conj_by_dilation k r (fun q => q.1.1.2) (continuous_snd.comp (continuous_fst.comp continuous_fst))
      (fun q => q.2.1) (continuous_fst.comp continuous_snd) (fun q hq => hq.2.1)
  · exact (continuous_fst.comp (continuous_snd.comp continuous_fst)).continuousOn
  · exact continuousOn_conj_by_dilation k r (fun q => q.1.2.2) (continuous_snd.comp (continuous_snd.comp continuous_fst))
      (fun q => q.2.2) (continuous_snd.comp continuous_snd) (fun q hq => hq.2.2)

theorem dilationAction_one (p : SS k r) : dilation₂ (1, 1) p = p := by
  have h : ∀ x : Mt k r, conjM (aDil k r 1) x = x := by
    intro x
    unfold conjM
    rw [aDil_one, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  unfold dilation₂
  simp only [h]

theorem inSS_mem (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r) ∈ GV k r ∧ (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ GV k r :=
  ⟨WeylGroupFacts.uh_mul (Nset_sub k r hp.2.1) (UWset_sub k r _ hp.1),
    WeylGroupFacts.uh_mul (Nset_sub k r hp.2.2.2) (UWset_sub k r _ hp.2.2.1)⟩

theorem sgs_eq (p : SS k r) (g : Mat k r) :
    sgs p g = (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) := by
  unfold sgs
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem sgs_dil (hU : DilUW) (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) (g : Mat k r) :
    sgs (dilation₂ (x, y) p) (aDil k r x * g * (aDil k r y)⁻¹) = aDil k r x * sgs p g * (aDil k r y)⁻¹ := by
  obtain ⟨⟨h, n⟩, ⟨h', n'⟩⟩ := p
  have ua := WeylGroupFacts.isUnit_of_uh (aDil_mem k r hx)
  have ub := WeylGroupFacts.isUnit_of_uh (aDil_mem k r hy)
  have uh := WeylGroupFacts.isUnit_of_uh (UWset_sub k r _ hp.1)
  have uh' := WeylGroupFacts.isUnit_of_uh (UWset_sub k r _ hp.2.2.1)
  have k1 : aDil k r x * (Matrix.of h : Mat k r) = Matrix.of h * aDil k r x := hU k r D.z x _ hp.1
  have k2 : aDil k r y * (Matrix.of h' : Mat k r) = Matrix.of h' * aDil k r y := hU k r D.z' y _ hp.2.2.1
  have c1 : (Matrix.of h : Mat k r)⁻¹ * aDil k r x = aDil k r x * (Matrix.of h : Mat k r)⁻¹ := by
    calc (Matrix.of h : Mat k r)⁻¹ * aDil k r x
        = (Matrix.of h : Mat k r)⁻¹ * (aDil k r x * Matrix.of h) * (Matrix.of h : Mat k r)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uh, Matrix.mul_one]
      _ = aDil k r x * (Matrix.of h : Mat k r)⁻¹ := by
          rw [k1, Matrix.nonsing_inv_mul_cancel_left _ _ uh]
  have c2 : (aDil k r y)⁻¹ * (Matrix.of h' : Mat k r) = Matrix.of h' * (aDil k r y)⁻¹ := by
    calc (aDil k r y)⁻¹ * (Matrix.of h' : Mat k r)
        = (aDil k r y)⁻¹ * (Matrix.of h' * aDil k r y) * (aDil k r y)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ub, Matrix.mul_one]
      _ = Matrix.of h' * (aDil k r y)⁻¹ := by
          rw [← k2, Matrix.nonsing_inv_mul_cancel_left _ _ ub]
  have e1 : (aDil k r x * (Matrix.of n : Mat k r) * (aDil k r x)⁻¹)⁻¹ =
      aDil k r x * (Matrix.of n : Mat k r)⁻¹ * (aDil k r x)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ua, Matrix.mul_assoc]
  show (Matrix.of h : Mat k r)⁻¹ * (aDil k r x * (Matrix.of n : Mat k r) * (aDil k r x)⁻¹)⁻¹ *
      (aDil k r x * g * (aDil k r y)⁻¹) * (aDil k r y * (Matrix.of n' : Mat k r) * (aDil k r y)⁻¹) *
      (Matrix.of h' : Mat k r) =
    aDil k r x * ((Matrix.of h : Mat k r)⁻¹ * (Matrix.of n : Mat k r)⁻¹ * g * Matrix.of n' * Matrix.of h') *
      (aDil k r y)⁻¹
  rw [e1]
  calc (Matrix.of h : Mat k r)⁻¹ * (aDil k r x * (Matrix.of n : Mat k r)⁻¹ * (aDil k r x)⁻¹) *
      (aDil k r x * g * (aDil k r y)⁻¹) * (aDil k r y * (Matrix.of n' : Mat k r) * (aDil k r y)⁻¹) *
      (Matrix.of h' : Mat k r)
      = ((Matrix.of h : Mat k r)⁻¹ * aDil k r x) * (Matrix.of n : Mat k r)⁻¹ * ((aDil k r x)⁻¹ * aDil k r x) * g *
        ((aDil k r y)⁻¹ * aDil k r y) * Matrix.of n' * ((aDil k r y)⁻¹ * Matrix.of h') := by
        simp only [Matrix.mul_assoc]
    _ = (aDil k r x * (Matrix.of h : Mat k r)⁻¹) * (Matrix.of n : Mat k r)⁻¹ * 1 * g * 1 * Matrix.of n' *
        (Matrix.of h' * (aDil k r y)⁻¹) := by
        rw [c1, c2, Matrix.nonsing_inv_mul _ ua, Matrix.nonsing_inv_mul _ ub]
    _ = aDil k r x * ((Matrix.of h : Mat k r)⁻¹ * (Matrix.of n : Mat k r)⁻¹ * g * Matrix.of n' * Matrix.of h') *
        (aDil k r y)⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.mul_one]

theorem lam_dil (hN : DilN) (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    lam k r D.z (Matrix.of (dilation₂ (x, y) p).1.2) = x * lam k r D.z (Matrix.of p.1.2) ∧
    lam k r D.z' (Matrix.of (dilation₂ (x, y) p).2.2) = y * lam k r D.z' (Matrix.of p.2.2) :=
  ⟨(hN k r D.z x hx.ne' D.z_mem _ hp.2.1).2.2, (hN k r D.z' y hy.ne' D.z'_mem _ hp.2.2.2).2.2⟩

end setting

section calcG

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smooth_on_mono {m m' : ℕ∞} (hm : m' ≤ m) {UU : Set (Mat k r)} {f : Mat k r → E} (h : CkOn m UU f) :
    CkOn m' UU f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast hm), he⟩

theorem continuousOn_of_contDiffOn_group {m : ℕ∞} {f : Mat k r → E} (h : CkOn m (GV k r) f) : ContinuousOn f (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  have h1 : ContinuousAt f' g₀ := hf'.continuousOn.continuousAt (hU.mem_nhds hgU)
  have h2 : ContinuousWithinAt f' (GV k r) g₀ := h1.continuousWithinAt
  refine h2.congr_of_eventuallyEq ?_ (he g₀ hgU hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hg1 hg2
  exact he g hg1 hg2

theorem contDiff_mul_right' (X : Mat k r) {n : WithTop ℕ∞} : ContDiff ℝ n (fun g : Mat k r => g * X) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff

theorem contDiff_matrix_mul_left (X : Mat k r) {n : WithTop ℕ∞} : ContDiff ℝ n (fun g : Mat k r => X * g) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)).contDiff

theorem hasDerivAt_right_flow_dilation_generator {f f' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hgU : g ∈ U)
    (hg : g ∈ GV k r) (hf' : DifferentiableAt ℝ f' g) (he : ∀ x ∈ U, x ∈ GV k r → f x = f' x) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X0 k r))) (fderiv ℝ f' g (g * X0 k r)) 0 := by
  have hγ := hasDerivAt_curveR (k := k) (r := r) g
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X0 k r) = g := by
    simp [NormedSpace.exp_zero]
  have hcomp : HasDerivAt (fun s : ℝ => f' (g * NormedSpace.exp ((s : ℂ) • X0 k r)))
      (fderiv ℝ f' g (g * X0 k r)) 0 :=
    hf'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ s : ℝ in 𝓝 0, g * NormedSpace.exp ((s : ℂ) • X0 k r) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
  filter_upwards [hmem] with s hs
  exact he _ hs (WeylGroupFacts.uh_mul hg (exp_mem k r s))

theorem left_derivative_has_deriv {f f' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hgU : g ∈ U)
    (hg : g ∈ GV k r) (hf' : DifferentiableAt ℝ f' g) (he : ∀ x ∈ U, x ∈ GV k r → f x = f' x) :
    HasDerivAt (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X0 k r)) * g))
      (fderiv ℝ f' g (-(X0 k r * g))) 0 := by
  have hγ := hasDerivAt_curveL (k := k) (r := r) g
  have hγ0 : NormedSpace.exp (-(((0 : ℝ) : ℂ) • X0 k r)) * g = g := by
    simp [NormedSpace.exp_zero]
  have hcomp : HasDerivAt (fun s : ℝ => f' (NormedSpace.exp (-((s : ℂ) • X0 k r)) * g))
      (fderiv ℝ f' g (-(X0 k r * g))) 0 :=
    hf'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ s : ℝ in 𝓝 0, NormedSpace.exp (-((s : ℂ) • X0 k r)) * g ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
  filter_upwards [hmem] with s hs
  exact he _ hs (WeylGroupFacts.uh_mul (exp_neg_mem k r s) hg)

theorem right_derivative_exists {n : ℕ} {f : Mat k r → E} (h : CkOn ((n + 1 : ℕ) : ℕ∞) (GV k r) f) : DR f := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by norm_cast)).differentiableAt (hU.mem_nhds hgU)
  have h1 := hasDerivAt_right_flow_dilation_generator hU hgU hg hd he
  have h2 : RdV (X0 k r) f g = fderiv ℝ f' g (g * X0 k r) := h1.deriv
  rw [h2]; exact h1

theorem differentiable_left_of_contDiffOn_succ {n : ℕ} {f : Mat k r → E} (h : CkOn ((n + 1 : ℕ) : ℕ∞) (GV k r) f) : DL f := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by norm_cast)).differentiableAt (hU.mem_nhds hgU)
  have h1 := left_derivative_has_deriv hU hgU hg hd he
  have h2 : LdV (X0 k r) f g = fderiv ℝ f' g (-(X0 k r * g)) := h1.deriv
  rw [h2]; exact h1

theorem smooth_right_derivative {n : ℕ} {f : Mat k r → E} (h : CkOn ((n + 1 : ℕ) : ℕ∞) (GV k r) f) :
    CkOn (n : ℕ∞) (GV k r) (Rr f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  refine ⟨U, fun g => fderiv ℝ f' g (g * X0 k r), hU, hgU, ?_, ?_⟩
  · exact ContDiffOn.clm_apply (hf'.fderiv_of_isOpen hU (m := ((n : ℕ∞) : WithTop ℕ∞)) (by norm_cast))
      (contDiff_mul_right' (X0 k r)).contDiffOn
  · intro g hgU' hg
    have hd : DifferentiableAt ℝ f' g :=
      (hf'.differentiableOn (by norm_cast)).differentiableAt (hU.mem_nhds hgU')
    exact (hasDerivAt_right_flow_dilation_generator hU hgU' hg hd he).deriv

theorem smooth_left_derivative {n : ℕ} {f : Mat k r → E} (h : CkOn ((n + 1 : ℕ) : ℕ∞) (GV k r) f) :
    CkOn (n : ℕ∞) (GV k r) (Ll f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  refine ⟨U, fun g => fderiv ℝ f' g (-(X0 k r * g)), hU, hgU, ?_, ?_⟩
  · exact ContDiffOn.clm_apply (hf'.fderiv_of_isOpen hU (m := ((n : ℕ∞) : WithTop ℕ∞)) (by norm_cast))
      (contDiff_matrix_mul_left (X0 k r)).neg.contDiffOn
  · intro g hgU' hg
    have hd : DifferentiableAt ℝ f' g :=
      (hf'.differentiableOn (by norm_cast)).differentiableAt (hU.mem_nhds hgU')
    exact (left_derivative_has_deriv hU hgU' hg hd he).deriv

theorem smooth_iterated_right_derivative {n : ℕ} (j : ℕ) : ∀ {f : Mat k r → E}, CkOn ((n + j : ℕ) : ℕ∞) (GV k r) f →
    CkOn (n : ℕ∞) (GV k r) (Rr^[j] f) := by
  induction j with
  | zero => intro f h; exact h
  | succ j ih =>
    intro f h
    exact ih (smooth_right_derivative (n := n + j) h)

theorem smooth_iterated_left_derivative {n : ℕ} (i : ℕ) : ∀ {f : Mat k r → E}, CkOn ((n + i : ℕ) : ℕ∞) (GV k r) f →
    CkOn (n : ℕ∞) (GV k r) (Ll^[i] f) := by
  induction i with
  | zero => intro f h; exact h
  | succ i ih =>
    intro f h
    exact ih (smooth_left_derivative (n := n + i) h)

theorem smooth_iterated_left_right_derivatives {n i j : ℕ} {f : Mat k r → E} (h : CkOn ((4 : ℕ) : ℕ∞) (GV k r) f) (hn : n + i + j ≤ 4) :
    CkOn (n : ℕ∞) (GV k r) (Ll^[i] (Rr^[j] f)) :=
  smooth_iterated_left_derivative i (smooth_iterated_right_derivative j (smooth_on_mono (by exact_mod_cast hn) h))

theorem foldr_replicate_iterate {β γ : Type*} (φ : β → γ → γ) (X : β) (a : γ) (i : ℕ) :
    (List.replicate i X).foldr φ a = (φ X)^[i] a := by
  induction i with
  | zero => rfl
  | succ i ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

theorem replicated_word_derivative (i j : ℕ) (f : Mat k r → E) :
    dLR (List.replicate i (X0 k r)) (List.replicate j (X0 k r)) f = Ll^[i] (Rr^[j] f) := by
  unfold dLR Rw
  rw [foldr_replicate_iterate, foldr_replicate_iterate]

theorem admissible_weighted_of_bound {α c : ℝ} {F : Mat k r → E} (h : CCle α 4 F c) : AdmW α c 2 2 F := by
  obtain ⟨hck, hb⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro j hj i hi
    refine ⟨continuousOn_of_contDiffOn_group (smooth_iterated_left_right_derivatives (n := 0) hck (by omega)), ?_⟩
    intro g hg
    rw [← replicated_word_derivative]
    refine hb _ _ ?_ ?_ ?_ g hg
    · intro X hX; rw [List.eq_of_mem_replicate hX]; exact lie_element_unitary k r
    · intro X hX; rw [List.eq_of_mem_replicate hX]; exact lie_element_unitary k r
    · simp only [List.length_replicate]; omega
  · intro j hj
    exact right_derivative_exists (n := 0) (smooth_iterated_left_right_derivatives (n := 1) (i := 0) hck (by omega))
  · intro j hj i hi
    exact differentiable_left_of_contDiffOn_succ (n := 0) (smooth_iterated_left_right_derivatives (n := 1) hck (by omega))

theorem admissibleWeight_right_derivative {α c : ℝ} {n m : ℕ} {f : Mat k r → E} (h : AdmW α c (n + 1) m f) : AdmW α c n m (Rr f) :=
  ⟨fun j hj i hi => h.1 (j + 1) (by omega) i hi, fun j hj => h.2.1 (j + 1) (by omega),
    fun j hj i hi => h.2.2 (j + 1) (by omega) i hi⟩

theorem admissible_weight_lower_order {α c : ℝ} {n m : ℕ} {f : Mat k r → E} (h : AdmW α c (n + 1) m f) : AdmW α c n m f :=
  ⟨fun j hj i hi => h.1 j (by omega) i hi, fun j hj => h.2.1 j (by omega),
    fun j hj i hi => h.2.2 j (by omega) i hi⟩

theorem admissibleWeight_left_derivative {α c : ℝ} {m : ℕ} {f : Mat k r → E} (h : AdmW α c 0 (m + 1) f) : AdmW α c 0 m (Ll f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj i hi
    obtain rfl : j = 0 := by omega
    exact h.1 0 le_rfl (i + 1) (by omega)
  · intro j hj; omega
  · intro j hj i hi
    obtain rfl : j = 0 := by omega
    exact h.2.2 0 le_rfl (i + 1) (by omega)

theorem admissibleWeight_of_succ_left_order {α c : ℝ} {n m : ℕ} {f : Mat k r → E} (h : AdmW α c n (m + 1) f) : AdmW α c n m f :=
  ⟨fun j hj i hi => h.1 j hj i (by omega), h.2.1, fun j hj i hi => h.2.2 j hj i (by omega)⟩

theorem admissible_of_weighted {α c : ℝ} {n m : ℕ} {f : Mat k r → E} (h : AdmW α c n m f) : admitted α c f :=
  h.1 0 (Nat.zero_le _) 0 (Nat.zero_le _)

end calcG

section hs

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hilbert_schmidt_inner_basis_sum (A B : Wq →L[ℂ] Wp) :
    hsInner A B = ∑ i, inner ℂ (B (stdOrthonormalBasis ℂ Wq i)) (A (stdOrthonormalBasis ℂ Wq i)) := by
  simp [hsInner, hsVec, PiLp.inner_apply]

theorem hsInner_norm_le (A B : Wq →L[ℂ] Wp) : ‖hsInner A B‖ ≤ (Module.finrank ℂ Wq : ℝ) * ‖A‖ * ‖B‖ := by
  rw [hilbert_schmidt_inner_basis_sum]
  calc ‖∑ i, inner ℂ (B (stdOrthonormalBasis ℂ Wq i)) (A (stdOrthonormalBasis ℂ Wq i))‖
      ≤ ∑ i : Fin (Module.finrank ℂ Wq), ‖A‖ * ‖B‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        have h1 : ‖B (stdOrthonormalBasis ℂ Wq i)‖ ≤ ‖B‖ := by
          simpa using B.le_opNorm (stdOrthonormalBasis ℂ Wq i)
        have h2 : ‖A (stdOrthonormalBasis ℂ Wq i)‖ ≤ ‖A‖ := by
          simpa using A.le_opNorm (stdOrthonormalBasis ℂ Wq i)
        calc _ ≤ ‖B (stdOrthonormalBasis ℂ Wq i)‖ * ‖A (stdOrthonormalBasis ℂ Wq i)‖ := norm_inner_le_norm _ _
          _ ≤ ‖B‖ * ‖A‖ := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
          _ = ‖A‖ * ‖B‖ := mul_comm _ _
    _ = (Module.finrank ℂ Wq : ℝ) * ‖A‖ * ‖B‖ := by
        simp [mul_assoc]

theorem hsInner_add_left (A A' B : Wq →L[ℂ] Wp) : hsInner (A + A') B = hsInner A B + hsInner A' B := by
  simp only [hilbert_schmidt_inner_basis_sum, _root_.add_apply, inner_add_right, Finset.sum_add_distrib]

theorem hsInner_add_right (A B B' : Wq →L[ℂ] Wp) : hsInner A (B + B') = hsInner A B + hsInner A B' := by
  simp only [hilbert_schmidt_inner_basis_sum, _root_.add_apply, inner_add_left, Finset.sum_add_distrib]

theorem hsInner_smul_left (a : ℂ) (A B : Wq →L[ℂ] Wp) : hsInner (a • A) B = a * hsInner A B := by
  simp only [hilbert_schmidt_inner_basis_sum, _root_.smul_apply, inner_smul_right, Finset.mul_sum]

theorem hsInner_smul_right (a : ℂ) (A B : Wq →L[ℂ] Wp) : hsInner A (a • B) = conj a * hsInner A B := by
  simp only [hilbert_schmidt_inner_basis_sum, _root_.smul_apply, inner_smul_left, Finset.mul_sum]

theorem hsInner_continuous : Continuous (fun P : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => hsInner P.1 P.2) := by
  simp only [hilbert_schmidt_inner_basis_sum]
  refine continuous_finsetSum _ fun i _ => ?_
  exact Continuous.inner (by fun_prop) (by fun_prop)

theorem hsInner_hasDerivAt {u v : ℝ → (Wq →L[ℂ] Wp)} {u' v' : Wq →L[ℂ] Wp} {y : ℝ} (hu : HasDerivAt u u' y)
    (hv : HasDerivAt v v' y) :
    HasDerivAt (fun s => hsInner (u s) (v s)) (hsInner u' (v y) + hsInner (u y) v') y := by
  simp only [hilbert_schmidt_inner_basis_sum, ← Finset.sum_add_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h1 : HasDerivAt (fun s => u s (stdOrthonormalBasis ℂ Wq i)) (u' (stdOrthonormalBasis ℂ Wq i)) y := by
    exact ((ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y hu
  have h2 : HasDerivAt (fun s => v s (stdOrthonormalBasis ℂ Wq i)) (v' (stdOrthonormalBasis ℂ Wq i)) y := by
    exact ((ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y hv
  exact h2.inner ℂ h1

def Sd (D : RealPlaceData k r Wp Wq) (p : SS k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
    ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹))

theorem Sd_apply (D : RealPlaceData k r Wp Wq) (p : SS k r) (X : Wq →L[ℂ] Wp) :
    Sd D p X = (D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹)) := rfl

theorem rho_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    rho D p F g = Sd D p (F (sgs p g)) := rfl

theorem opNorm_le_one_of_norm_map_eq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (T : W →L[ℂ] W)
    (h : ∀ v, ‖T v‖ = ‖v‖) : ‖T‖ ≤ 1 :=
  T.opNorm_le_bound zero_le_one fun v => by rw [h v, one_mul]

theorem Sd_norm_le (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Wq →L[ℂ] Wp) :
    ‖Sd D p X‖ ≤ ‖X‖ := by
  rw [Sd_apply]
  have h1 : ‖D.π (Matrix.of p.1.1)‖ ≤ 1 := opNorm_le_one_of_norm_map_eq _ (D.π_unitary _ hp.1)
  have h2 : ‖D.π' (Matrix.of p.2.1)⁻¹‖ ≤ 1 := opNorm_le_one_of_norm_map_eq _ (D.π'_unitary _ (WeylGroupFacts.uw_inv hp.2.2.1))
  calc _ ≤ ‖D.π (Matrix.of p.1.1)‖ * ‖X.comp (D.π' (Matrix.of p.2.1)⁻¹)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖X‖ * ‖D.π' (Matrix.of p.2.1)⁻¹‖) :=
        mul_le_mul h1 (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ 1 * (‖X‖ * 1) := by gcongr
    _ = ‖X‖ := by ring

theorem Sd_dil (D : RealPlaceData k r Wp Wq) (p : SS k r) (t : ℝ × ℝ) : Sd D (dilation₂ t p) = Sd D p := rfl

theorem continuous_first_coordinate_matrix : Continuous (fun p : SS k r => (Matrix.of p.1.1 : Mat k r)) := continuous_fst.fst
theorem continuous_matrix_coordinate_projection : Continuous (fun p : SS k r => (Matrix.of p.1.2 : Mat k r)) := continuous_fst.snd
theorem continuous_third_coordinate : Continuous (fun p : SS k r => (Matrix.of p.2.1 : Mat k r)) := continuous_snd.fst
theorem continuous_fourth_coordinate : Continuous (fun p : SS k r => (Matrix.of p.2.2 : Mat k r)) := continuous_snd.snd

theorem Sd_continuousOn (D : RealPlaceData k r Wp Wq) : ContinuousOn (fun p : SS k r => Sd D p) {p | D.inSS p} := by
  have h1 : ContinuousOn (fun p : SS k r => D.π (Matrix.of p.1.1)) {p | D.inSS p} :=
    D.π_cont.comp continuous_first_coordinate_matrix.continuousOn (fun p hp => hp.1)
  have h2 : ContinuousOn (fun p : SS k r => D.π' (Matrix.of p.2.1)⁻¹) {p | D.inSS p} :=
    D.π'_cont.comp ((inv_continuousOn k r).comp continuous_third_coordinate.continuousOn
      (fun p hp => UWset_sub _ _ _ hp.2.2.1)) (fun p hp => WeylGroupFacts.uw_inv hp.2.2.1)
  exact ((ContinuousLinearMap.compL ℂ Wq Wp Wp).continuous.comp_continuousOn h1).clm_comp
    (((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip).continuous.comp_continuousOn h2)

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem scaled_operator_norm (T : Wq →L[ℂ] Wp) (hT : ‖T‖ = 1) (g : Mat k r) :
    ‖((gN g ^ (-α) : ℝ) : ℂ) • T‖ = gN g ^ (-α) := by
  rw [norm_smul, hT, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (gN_nonneg g) _)]

theorem adm_gN_rpow_neg_smul_of_norm_eq_one (T : Wq →L[ℂ] Wp) (hT : ‖T‖ = 1) :
    admitted α 1 (fun g : Mat k r => ((gN g ^ (-α) : ℝ) : ℂ) • T) := by
  refine ⟨?_, fun g hg => ?_⟩
  · have h1 : ContinuousOn (fun g : Mat k r => gN g ^ (-α)) (GV k r) :=
      gN_continuous.continuousOn.rpow_const (fun g hg => Or.inl (gN_pos hg).ne')
    exact (Complex.continuous_ofReal.comp_continuousOn h1).smul continuousOn_const
  · rw [scaled_operator_norm T hT, ← Real.rpow_add (gN_pos hg)]
    simp

theorem translated_product_integrable_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
    admitted α cA A → admitted α cB B → ∀ x ∈ GV k r, ∀ y ∈ GV k r,
      Integrable (fun g : Mt k r => ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖) D.μG ∧
      (∫ g : Mt k r, ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖ ∂D.μG) ≤
        K * cA * cB * ((Ξ x : ℝ) * (Ξ y : ℝ)) := by
  obtain ⟨C, hC⟩ := H.coef
  refine ⟨max C 0, le_max_right _ _, fun A B cA cB hA hB x hx y hy => ?_⟩
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  have hL := hC A B cA cB (admissible_ae_strongly_measurable hA D.haarG) (admissible_ae_strongly_measurable hB D.haarG) hA.2 hB.2 x hx y hy
  have hAt : AEStronglyMeasurable (fun g : Mt k r => A (x⁻¹ * Matrix.of g * y)) D.μG :=
    admissible_ae_strongly_measurable (admissible_two_sided_translate H.α_nonneg hA (WeylGroupFacts.uh_inv hx) hy) D.haarG
  have hm : AEStronglyMeasurable (fun g : Mt k r => ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖) D.μG :=
    hAt.norm.mul (admissible_ae_strongly_measurable hB D.haarG).norm
  have he : ∀ g : Mt k r, ENNReal.ofReal (‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖) =
      ‖A (x⁻¹ * Matrix.of g * y)‖ₑ * ‖B (Matrix.of g)‖ₑ := fun g => by
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  have hfin : ENNReal.ofReal (C * cA * cB) * (Ξ x : ℝ≥0∞) * (Ξ y : ℝ≥0∞) < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top) ENNReal.coe_lt_top
  have hnn : ∀ g : Mt k r, 0 ≤ ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖ := fun g => by positivity
  constructor
  · refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)]
    simp only [he]
    exact lt_of_le_of_lt hL hfin
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hm]
    simp only [he]
    refine (ENNReal.toReal_mono hfin.ne hL).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [ENNReal.toReal_ofReal']
    refine max_le ?_ (by positivity)
    have : C ≤ max C 0 := le_max_left _ _
    gcongr

theorem model_integrable (H : Hyp D Ξ α) :
    Integrable (fun g : Mt k r => gN (Matrix.of g : Mat k r) ^ (-α) * gN (Matrix.of g : Mat k r) ^ (-α)) D.μG := by
  obtain ⟨T, hT⟩ := H.T0
  obtain ⟨K, -, hK⟩ := translated_product_integrable_bound H
  have h := (hK _ _ 1 1 (adm_gN_rpow_neg_smul_of_norm_eq_one (α := α) T hT) (adm_gN_rpow_neg_smul_of_norm_eq_one (α := α) T hT) 1 WeylGroupFacts.uh_one 1 WeylGroupFacts.uh_one).1
  simpa only [scaled_operator_norm T hT, inv_one, Matrix.one_mul, Matrix.mul_one] using h

theorem aestronglyMeasurable_hilbertSchmidt_rho_integrand (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) :
    AEStronglyMeasurable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  have hxy := inSS_mem D hp
  have hAt : AEStronglyMeasurable (fun g : Mt k r => A (sgs p (Matrix.of g))) D.μG := by
    simp only [sgs_eq]
    exact admissible_ae_strongly_measurable (admissible_two_sided_translate H.α_nonneg hA (WeylGroupFacts.uh_inv hxy.1) hxy.2) D.haarG
  have h1 : AEStronglyMeasurable (fun g : Mt k r => Sd D p (A (sgs p (Matrix.of g)))) D.μG :=
    (Sd D p).continuous.comp_aestronglyMeasurable hAt
  exact hsInner_continuous.comp_aestronglyMeasurable (h1.prodMk (admissible_ae_strongly_measurable hB D.haarG))

theorem hilbert_schmidt_integrand_bound (D : RealPlaceData k r Wp Wq) (A B : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r}
    (hp : D.inSS p) (g : Mat k r) :
    ‖hsInner (rho D p A g) (B g)‖ ≤ (Module.finrank ℂ Wq : ℝ) *
      (‖A ((Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ * ‖B g‖) := by
  rw [rho_eq, ← sgs_eq, ← mul_assoc]
  refine (hsInner_norm_le _ _).trans ?_
  have := Sd_norm_le D hp (A (sgs p g))
  gcongr

theorem ph_integrable (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) :
    Integrable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  obtain ⟨K, -, hK⟩ := translated_product_integrable_bound H
  have hxy := inSS_mem D hp
  have h := (hK A B cA cB hA hB _ hxy.1 _ hxy.2).1
  exact (h.const_mul (Module.finrank ℂ Wq : ℝ)).mono' (aestronglyMeasurable_hilbertSchmidt_rho_integrand H hA hB hp)
    (Eventually.of_forall fun g => hilbert_schmidt_integrand_bound D A B hp _)

theorem ph_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
    admitted α cA A → admitted α cB B → ∀ p, D.inSS p → ‖Ph D A B p‖ ≤ K * cA * cB * XX Ξ p := by
  obtain ⟨K, hK0, hK⟩ := translated_product_integrable_bound H
  refine ⟨(Module.finrank ℂ Wq : ℝ) * K, by positivity, fun A B cA cB hA hB p hp => ?_⟩
  have hxy := inSS_mem D hp
  have h := hK A B cA cB hA hB _ hxy.1 _ hxy.2
  unfold Ph
  refine (norm_integral_le_of_norm_le (h.1.const_mul (Module.finrank ℂ Wq : ℝ))
    (Eventually.of_forall fun g => hilbert_schmidt_integrand_bound D A B hp _)).trans ?_
  rw [integral_const_mul]
  calc (Module.finrank ℂ Wq : ℝ) * _ ≤ (Module.finrank ℂ Wq : ℝ) * (K * cA * cB * XX Ξ p) :=
        mul_le_mul_of_nonneg_left h.2 (by positivity)
    _ = _ := by ring

theorem continuous_right_multiplication_map (a : Mat k r) : Continuous (rmulF a) := by
  unfold rmulF
  exact continuous_id.matrix_mul continuous_const

def rightMulMeasurableEquiv (a : Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulF a
  invFun := rmulF a⁻¹
  left_inv x := by
    have : Matrix.of x * a * a⁻¹ = Matrix.of x := Matrix.mul_nonsing_inv_cancel_right _ _ ha
    exact this
  right_inv x := by
    have : Matrix.of x * a⁻¹ * a = Matrix.of x := Matrix.nonsing_inv_mul_cancel_right _ _ ha
    exact this
  measurable_toFun := (continuous_right_multiplication_map a).measurable
  measurable_invFun := (continuous_right_multiplication_map a⁻¹).measurable

theorem ph_dil (H : Hyp D Ξ α) (A B : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Ph D A B (dilation₂ (x, y) p) =
      Ph D (fun g => A (aDil k r x * g * (aDil k r y)⁻¹)) (fun g => B (aDil k r x * g * (aDil k r y)⁻¹)) p := by
  have hax := aDil_mem k r hx
  have hay := aDil_inv_mem k r hy
  have mpL : MeasurePreserving (lmulM (aDil k r x)) D.μG D.μG :=
    ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarG.left _ hax⟩
  have mpR : MeasurePreserving (rmulF (aDil k r y)⁻¹) D.μG D.μG :=
    ⟨(continuous_right_multiplication_map _).measurable, D.haarG.right _ hay⟩
  have eL : MeasurableEmbedding (lmulM (k := k) (r := r) (aDil k r x)) :=
    (BesselUnitaryEquiv.lmulE _ (WeylGroupFacts.isUnit_of_uh hax)).measurableEmbedding
  have eR : MeasurableEmbedding (rmulF (aDil k r y)⁻¹) :=
    (rightMulMeasurableEquiv _ (WeylGroupFacts.isUnit_of_uh hay)).measurableEmbedding
  unfold Ph
  rw [← (mpR.comp mpL).integral_comp (eR.comp eL)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have e : (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g) : Mat k r) =
      aDil k r x * Matrix.of g * (aDil k r y)⁻¹ := rfl
  show hsInner (rho D (dilation₂ (x, y) p) A (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g)))
      (B (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g))) =
    hsInner (rho D p (fun g => A (aDil k r x * g * (aDil k r y)⁻¹)) (Matrix.of g))
      (B (aDil k r x * Matrix.of g * (aDil k r y)⁻¹))
  rw [e, rho_eq, rho_eq, sgs_dil H.dilUW D hp hx hy, Sd_dil]

theorem phdil_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
    admitted α cA A → admitted α cB B → ∀ p, D.inSS p → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, ∀ y ∈ Set.Icc (1 / 2 : ℝ) 2,
      ‖Ph D A B (dilation₂ (x, y) p)‖ ≤ K * cA * cB * XX Ξ p := by
  obtain ⟨K, hK0, hK⟩ := ph_bound H
  obtain ⟨M, hM0, hM⟩ := aDil_gN_bound k r (a := 1 / 2) (b := 2) (by norm_num)
  refine ⟨K * ((M * M) ^ α * (M * M) ^ α), by positivity, fun A B cA cB hA hB p hp x hx y hy => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
  have hax := aDil_mem k r hx0
  have hay := aDil_inv_mem k r hy0
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  rw [ph_dil H A B hp hx0 hy0]
  have h := hK _ _ _ _ (admissible_two_sided_translate H.α_nonneg hA hax hay) (admissible_two_sided_translate H.α_nonneg hB hax hay) p hp
  refine h.trans ?_
  have hXX : 0 ≤ XX Ξ p := by unfold XX; positivity
  have he : (gN (aDil k r x)⁻¹ * gN (aDil k r y)⁻¹⁻¹) ^ α ≤ (M * M) ^ α := by
    rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh (aDil_mem k r hy0))]
    exact Real.rpow_le_rpow (mul_nonneg (gN_nonneg _) (gN_nonneg _))
      (mul_le_mul (hM x hx).2 (hM y hy).1 (gN_nonneg _) hM0) H.α_nonneg
  have he0 : 0 ≤ (gN (aDil k r x)⁻¹ * gN (aDil k r y)⁻¹⁻¹) ^ α :=
    Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _
  calc K * (cA * (gN (aDil k r x)⁻¹ * gN (aDil k r y)⁻¹⁻¹) ^ α) *
        (cB * (gN (aDil k r x)⁻¹ * gN (aDil k r y)⁻¹⁻¹) ^ α) * XX Ξ p
      ≤ K * (cA * (M * M) ^ α) * (cB * (M * M) ^ α) * XX Ξ p := by gcongr
    _ = _ := by ring

theorem continuousOn_matrix_mul {X : Type*} [TopologicalSpace X] {s : Set X} {f g : X → Mat k r}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => f x * g x) s :=
  (continuous_fst.matrix_mul continuous_snd :
    Continuous fun P : Mat k r × Mat k r => P.1 * P.2).comp_continuousOn (hf.prodMk hg)

theorem conjugated_pair_continuous_on (D : RealPlaceData k r Wp Wq) (g : Mat k r) :
    ContinuousOn (fun p : SS k r => sgs p g) {p | D.inSS p} := by
  unfold sgs
  have i1 : ContinuousOn (fun p : SS k r => (Matrix.of p.1.1 : Mat k r)⁻¹) {p | D.inSS p} :=
    (inv_continuousOn k r).comp continuous_first_coordinate_matrix.continuousOn (fun p hp => UWset_sub _ _ _ hp.1)
  have i2 : ContinuousOn (fun p : SS k r => (Matrix.of p.1.2 : Mat k r)⁻¹) {p | D.inSS p} :=
    (inv_continuousOn k r).comp continuous_matrix_coordinate_projection.continuousOn (fun p hp => Nset_sub _ _ hp.2.1)
  exact continuousOn_matrix_mul (continuousOn_matrix_mul (continuousOn_matrix_mul (continuousOn_matrix_mul i1 i2)
    continuousOn_const) continuous_fourth_coordinate.continuousOn) continuous_third_coordinate.continuousOn

theorem conj_product_mem_unitary_group (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {g : Mat k r} (hg : g ∈ GV k r) :
    sgs p g ∈ GV k r := by
  have hxy := inSS_mem D hp
  rw [sgs_eq]
  exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hxy.1) hg) hxy.2

def normProductOfPair (p : SS k r) : ℝ :=
  gN (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r) * gN (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹

theorem norm_product_continuous_on (D : RealPlaceData k r Wp Wq) : ContinuousOn (normProductOfPair (k := k) (r := r)) {p | D.inSS p} := by
  unfold normProductOfPair
  have h1 : ContinuousOn (fun p : SS k r => (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)) {p | D.inSS p} :=
    continuousOn_matrix_mul continuous_matrix_coordinate_projection.continuousOn continuous_first_coordinate_matrix.continuousOn
  have h2 : ContinuousOn (fun p : SS k r => (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)) {p | D.inSS p} :=
    continuousOn_matrix_mul continuous_fourth_coordinate.continuousOn continuous_third_coordinate.continuousOn
  have h3 : ContinuousOn (fun p : SS k r => (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹) {p | D.inSS p} :=
    (inv_continuousOn k r).comp h2 (fun p hp => (inSS_mem D hp).2)
  exact (gN_continuous.comp_continuousOn h1).mul (gN_continuous.comp_continuousOn h3)

theorem norm_hilbertSchmidt_rho_pointwise_le (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) {g : Mat k r} (hg : g ∈ GV k r) {M : ℝ} (hM : normProductOfPair p ≤ M) :
    ‖hsInner (rho D p A g) (B g)‖ ≤
      (Module.finrank ℂ Wq : ℝ) * (cA * M ^ α * cB) * (gN g ^ (-α) * gN g ^ (-α)) := by
  have hxy := inSS_mem D hp
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  have h1 := admissible_norm_bound (admissible_two_sided_translate H.α_nonneg hA (WeylGroupFacts.uh_inv hxy.1) hxy.2) hg
  rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hxy.1)] at h1
  have h2 := admissible_norm_bound hB hg
  have h3 : (gN (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r) *
      gN (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹) ^ α ≤ M ^ α :=
    Real.rpow_le_rpow (mul_nonneg (gN_nonneg _) (gN_nonneg _)) hM H.α_nonneg
  have hg0 : 0 ≤ gN g ^ (-α) := Real.rpow_nonneg (gN_nonneg g) _
  have hM0 : 0 ≤ M ^ α := le_trans (Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _) h3
  refine (hilbert_schmidt_integrand_bound D A B hp g).trans ?_
  calc (Module.finrank ℂ Wq : ℝ) * (‖A ((Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ * g *
        (Matrix.of p.2.2 * Matrix.of p.2.1))‖ * ‖B g‖)
      ≤ (Module.finrank ℂ Wq : ℝ) * ((cA * M ^ α * gN g ^ (-α)) * (cB * gN g ^ (-α))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity))
          (by positivity)
        gcongr
    _ = _ := by ring

theorem ph_continuousOn (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) : ContinuousOn (Ph D A B) {p | D.inSS p} := by
  intro p₀ hp₀
  show ContinuousWithinAt (fun p => ∫ g : Mt k r, hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g)) ∂D.μG)
    {p | D.inSS p} p₀
  refine continuousWithinAt_of_dominated
    (bound := fun g : Mt k r => (Module.finrank ℂ Wq : ℝ) * (cA * (normProductOfPair p₀ + 1) ^ α * cB) *
      (gN (Matrix.of g : Mat k r) ^ (-α) * gN (Matrix.of g : Mat k r) ^ (-α))) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact aestronglyMeasurable_hilbertSchmidt_rho_integrand H hA hB hp
  · have hN : ∀ᶠ p in 𝓝[{p | D.inSS p}] p₀, normProductOfPair p < normProductOfPair p₀ + 1 :=
      (norm_product_continuous_on D p₀ hp₀).tendsto.eventually_lt_const (lt_add_one _)
    filter_upwards [self_mem_nhdsWithin, hN] with p hp hNp
    filter_upwards [haar_ae D.haarG] with g hg
    exact norm_hilbertSchmidt_rho_pointwise_le H hA hB hp hg hNp.le
  · exact (model_integrable H).const_mul _
  · filter_upwards [haar_ae D.haarG] with g hg
    have h1 : ContinuousWithinAt (fun p : SS k r => A (sgs p (Matrix.of g))) {p | D.inSS p} p₀ :=
      (hA.1.comp (conjugated_pair_continuous_on D (Matrix.of g)) (fun p hp => conj_product_mem_unitary_group D hp hg)) p₀ hp₀
    have h2 : ContinuousWithinAt (fun p : SS k r => Sd D p (A (sgs p (Matrix.of g)))) {p | D.inSS p} p₀ :=
      (Sd_continuousOn D p₀ hp₀).clm_apply h1
    exact hsInner_continuous.continuousAt.comp_continuousWithinAt (h2.prodMk continuousWithinAt_const)

end hs

section phd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hilbert_schmidt_pairing_measurable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) {a b : X → (Wq →L[ℂ] Wp)} (ha : AEStronglyMeasurable a μ)
    (hb : AEStronglyMeasurable b μ) : AEStronglyMeasurable (fun g => hsInner (L (a g)) (b g)) μ := by
  have h1 : AEStronglyMeasurable (fun g => L (a g)) μ := L.continuous.comp_aestronglyMeasurable ha
  have h2 : AEStronglyMeasurable (fun g => (L (a g), b g)) μ := h1.prodMk hb
  have h3 := (hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_aestronglyMeasurable h2
  exact h3

theorem norm_hilbertSchmidt_inner_contraction_le (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (hL : ∀ T, ‖L T‖ ≤ ‖T‖) {a b : Wq →L[ℂ] Wp}
    {C t : ℝ} (ha : ‖a‖ ≤ C * t) (hb : ‖b‖ ≤ C * t) :
    ‖hsInner (L a) b‖ ≤ (Module.finrank ℂ Wq : ℝ) * C ^ 2 * (t * t) := by
  have hd0 : (0 : ℝ) ≤ (Module.finrank ℂ Wq : ℝ) := by positivity
  have h0 : 0 ≤ C * t := le_trans (norm_nonneg _) ha
  calc ‖hsInner (L a) b‖ ≤ (Module.finrank ℂ Wq : ℝ) * ‖L a‖ * ‖b‖ := hsInner_norm_le _ _
    _ ≤ (Module.finrank ℂ Wq : ℝ) * (C * t) * (C * t) := by
        have h1 : ‖L a‖ ≤ C * t := le_trans (hL a) ha
        have : (Module.finrank ℂ Wq : ℝ) * ‖L a‖ ≤ (Module.finrank ℂ Wq : ℝ) * (C * t) :=
          mul_le_mul_of_nonneg_left h1 hd0
        exact mul_le_mul this hb (norm_nonneg _) (mul_nonneg hd0 h0)
    _ = (Module.finrank ℂ Wq : ℝ) * C ^ 2 * (t * t) := by ring

theorem hilbert_schmidt_pairing_deriv (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) {u v : ℝ → (Wq →L[ℂ] Wp)}
    {u' v' : Wq →L[ℂ] Wp} {y : ℝ} (hu : HasDerivAt u u' y) (hv : HasDerivAt v v' y) :
    HasDerivAt (fun s => hsInner (L (u s)) (v s)) (hsInner (L u') (v y) + hsInner (L (u y)) v') y := by
  have hLu : HasDerivAt (fun y => L (u y)) (L u') y :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y hu
  exact hsInner_hasDerivAt hLu hv

theorem parametric_derivative_under_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (hL : ∀ T, ‖L T‖ ≤ ‖T‖)
    {u v u' v' : ℝ → X → (Wq →L[ℂ] Wp)} {y₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 y₀) {m : X → ℝ} {C : ℝ}
    (hm : Integrable (fun g => m g * m g) μ)
    (mu : ∀ y ∈ s, AEStronglyMeasurable (u y) μ) (mv : ∀ y ∈ s, AEStronglyMeasurable (v y) μ)
    (mu' : ∀ y ∈ s, AEStronglyMeasurable (u' y) μ) (mv' : ∀ y ∈ s, AEStronglyMeasurable (v' y) μ)
    (du : ∀ᵐ g ∂μ, ∀ y ∈ s, HasDerivAt (fun y => u y g) (u' y g) y)
    (dv : ∀ᵐ g ∂μ, ∀ y ∈ s, HasDerivAt (fun y => v y g) (v' y g) y)
    (bu : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖u y g‖ ≤ C * m g) (bv : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖v y g‖ ≤ C * m g)
    (bu' : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖u' y g‖ ≤ C * m g) (bv' : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖v' y g‖ ≤ C * m g) :
    HasDerivAt (fun y => ∫ g, hsInner (L (u y g)) (v y g) ∂μ)
      (∫ g, (hsInner (L (u' y₀ g)) (v y₀ g) + hsInner (L (u y₀ g)) (v' y₀ g)) ∂μ) y₀ := by
  have hy₀ : y₀ ∈ s := mem_of_mem_nhds hs
  have c1 : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (fun g => hsInner (L (u y g)) (v y g)) μ := by
    filter_upwards [hs] with y hy using hilbert_schmidt_pairing_measurable L (mu y hy) (mv y hy)
  have c2 : Integrable (fun g => hsInner (L (u y₀ g)) (v y₀ g)) μ := by
    refine Integrable.mono' (hm.const_mul ((Module.finrank ℂ Wq : ℝ) * C ^ 2))
      (hilbert_schmidt_pairing_measurable L (mu y₀ hy₀) (mv y₀ hy₀)) ?_
    filter_upwards [bu, bv] with g h1 h2
    exact norm_hilbertSchmidt_inner_contraction_le L hL (h1 y₀ hy₀) (h2 y₀ hy₀)
  have c3 : AEStronglyMeasurable
      (fun g => hsInner (L (u' y₀ g)) (v y₀ g) + hsInner (L (u y₀ g)) (v' y₀ g)) μ :=
    (hilbert_schmidt_pairing_measurable L (mu' y₀ hy₀) (mv y₀ hy₀)).add (hilbert_schmidt_pairing_measurable L (mu y₀ hy₀) (mv' y₀ hy₀))
  have c4 : ∀ᵐ g ∂μ, ∀ y ∈ s, ‖hsInner (L (u' y g)) (v y g) + hsInner (L (u y g)) (v' y g)‖ ≤
      2 * ((Module.finrank ℂ Wq : ℝ) * C ^ 2) * (m g * m g) := by
    filter_upwards [bu, bv, bu', bv'] with g h1 h2 h3 h4
    intro y hy
    calc ‖hsInner (L (u' y g)) (v y g) + hsInner (L (u y g)) (v' y g)‖
        ≤ ‖hsInner (L (u' y g)) (v y g)‖ + ‖hsInner (L (u y g)) (v' y g)‖ := norm_add_le _ _
      _ ≤ (Module.finrank ℂ Wq : ℝ) * C ^ 2 * (m g * m g) + (Module.finrank ℂ Wq : ℝ) * C ^ 2 * (m g * m g) :=
          add_le_add (norm_hilbertSchmidt_inner_contraction_le L hL (h3 y hy) (h2 y hy)) (norm_hilbertSchmidt_inner_contraction_le L hL (h1 y hy) (h4 y hy))
      _ = 2 * ((Module.finrank ℂ Wq : ℝ) * C ^ 2) * (m g * m g) := by ring
  have c5 : Integrable (fun g => 2 * ((Module.finrank ℂ Wq : ℝ) * C ^ 2) * (m g * m g)) μ := hm.const_mul _
  have c6 : ∀ᵐ g ∂μ, ∀ y ∈ s, HasDerivAt (fun y => hsInner (L (u y g)) (v y g))
      (hsInner (L (u' y g)) (v y g) + hsInner (L (u y g)) (v' y g)) y := by
    filter_upwards [du, dv] with g h1 h2
    intro y hy
    exact hilbert_schmidt_pairing_deriv L (h1 y hy) (h2 y hy)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs c1 c2 c3 c4 c5 c6).2

theorem norm_admissible_of_double_translate_le {α c : ℝ} (hα : 0 ≤ α) {f : Mat k r → (Wq →L[ℂ] Wp)} (hf : admitted α c f)
    {u v g : Mat k r} (hu : u ∈ GV k r) (hv : v ∈ GV k r) (hg : g ∈ GV k r) {K : ℝ}
    (h1 : gN u⁻¹ ≤ K) (h2 : gN v⁻¹ ≤ K) :
    ‖f (u * g * v)‖ ≤ c * (K * K) ^ α * gN g ^ (-α) := by
  have h := admissible_norm_bound (admissible_two_sided_translate hα hf hu hv) hg
  have hc := admissible_constant_nonneg hf
  have hm : 0 ≤ gN g ^ (-α) := Real.rpow_nonneg (gN_nonneg g) _
  have hP : (gN u⁻¹ * gN v⁻¹) ^ α ≤ (K * K) ^ α :=
    Real.rpow_le_rpow (mul_nonneg (gN_nonneg _) (gN_nonneg _))
      (mul_le_mul h1 h2 (gN_nonneg _) (le_trans (gN_nonneg _) h1)) hα
  refine le_trans h ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hc) hm

theorem translated_norm_bound {α c : ℝ} (hα : 0 ≤ α) {f : Mat k r → (Wq →L[ℂ] Wp)} (hf : admitted α c f)
    {u v u₂ v₂ g : Mat k r} (hu : u ∈ GV k r) (hv : v ∈ GV k r) (hu₂ : u₂ ∈ GV k r) (hv₂ : v₂ ∈ GV k r)
    (hg : g ∈ GV k r) {K : ℝ} (h1 : gN u⁻¹ ≤ K) (h2 : gN v⁻¹ ≤ K) :
    ‖f (u * (u₂ * g * v₂) * v)‖ ≤ c * (K * K) ^ α * (gN u₂⁻¹ * gN v₂⁻¹) ^ α * gN g ^ (-α) := by
  have h := admissible_norm_bound (admissible_two_sided_translate hα (admissible_two_sided_translate hα hf hu hv) hu₂ hv₂) hg
  have hc := admissible_constant_nonneg hf
  have hm : 0 ≤ gN g ^ (-α) := Real.rpow_nonneg (gN_nonneg g) _
  have hM : 0 ≤ (gN u₂⁻¹ * gN v₂⁻¹) ^ α := Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _
  have hP : (gN u⁻¹ * gN v⁻¹) ^ α ≤ (K * K) ^ α :=
    Real.rpow_le_rpow (mul_nonneg (gN_nonneg _) (gN_nonneg _))
      (mul_le_mul h1 h2 (gN_nonneg _) (le_trans (gN_nonneg _) h1)) hα
  refine le_trans h ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hc) hM) hm

theorem product_bound_monotone_factors_le {e c P M' K c₀ M m : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 + K) (hc0 : 0 ≤ c) (hc : c ≤ c₀)
    (hP : 0 ≤ P) (hM0 : 0 ≤ M') (hM : M' ≤ 1 + M) (hm : 0 ≤ m) :
    e * (c * P * M' * m) ≤ (1 + K) * c₀ * P * (1 + M) * m := by
  have h1 : e * c ≤ (1 + K) * c₀ := mul_le_mul he hc hc0 (le_trans he0 he)
  have h2 : e * c * P ≤ (1 + K) * c₀ * P := mul_le_mul_of_nonneg_right h1 hP
  have h3 : e * c * P * M' ≤ (1 + K) * c₀ * P * (1 + M) :=
    mul_le_mul h2 hM hM0 (le_trans (mul_nonneg (mul_nonneg he0 hc0) hP) h2)
  calc e * (c * P * M' * m) = e * c * P * M' * m := by ring
    _ ≤ (1 + K) * c₀ * P * (1 + M) * m := mul_le_mul_of_nonneg_right h3 hm

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem pairing_derivative_locally_dominated (H : Hyp D Ξ α) {A B A1 B1 : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : admitted α cA A) (hA1 : admitted α cA A1) (hB : admitted α cB B) (hB1 : admitted α cB B1)
    {p : SS k r} (hp : D.inSS p) {a b : ℝ → Mat k r} {κ : ℝ → ℝ} {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    {K : ℝ} (ha : ∀ t ∈ s, a t ∈ GV k r) (hb : ∀ t ∈ s, b t ∈ GV k r)
    (hKa : ∀ t ∈ s, gN (a t)⁻¹ ≤ K) (hKb : ∀ t ∈ s, gN (b t)⁻¹ ≤ K) (hκ : ∀ t ∈ s, |κ t| ≤ K)
    (dA : ∀ z ∈ GV k r, ∀ t ∈ s, HasDerivAt (fun t => A (a t * z * b t)) (κ t • A1 (a t * z * b t)) t)
    (dB : ∀ z ∈ GV k r, ∀ t ∈ s, HasDerivAt (fun t => B (a t * z * b t)) (κ t • B1 (a t * z * b t)) t) :
    HasDerivAt (fun t => Ph D (fun g => A (a t * g * b t)) (fun g => B (a t * g * b t)) p)
      ((κ t₀ : ℂ) * (Ph D (fun g => A1 (a t₀ * g * b t₀)) (fun g => B (a t₀ * g * b t₀)) p +
        Ph D (fun g => A (a t₀ * g * b t₀)) (fun g => B1 (a t₀ * g * b t₀)) p)) t₀ := by
  have hα := H.α_nonneg
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  obtain ⟨hS1, hS2⟩ := inSS_mem D hp
  have hS1i := WeylGroupFacts.uh_inv hS1
  have hK0 : 0 ≤ K := le_trans (gN_nonneg _) (hKa t₀ ht₀)
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  obtain ⟨S1, hS1d⟩ : ∃ S1 : Mat k r, S1 = (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ := ⟨_, rfl⟩
  obtain ⟨S2, hS2d⟩ : ∃ S2 : Mat k r, S2 = (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) := ⟨_, rfl⟩
  rw [← hS1d] at hS1i
  rw [← hS2d] at hS2
  have hsgs : ∀ g : Mat k r, sgs p g = S1 * g * S2 := by
    intro g; rw [sgs_eq, hS1d, hS2d]
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = (K * K) ^ α := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = (gN S1⁻¹ * gN S2⁻¹) ^ α := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPd]; exact Real.rpow_nonneg (mul_nonneg hK0 hK0) _
  have hM0 : 0 ≤ M := by rw [hMd]; exact Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _
  have hG := haar_ae D.haarG

  have ms2 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ t ∈ s,
      AEStronglyMeasurable (fun g : Mt k r => f (a t * sgs p (Matrix.of g) * b t)) D.μG := by
    intro f c hf t ht
    have := admissible_ae_strongly_measurable (admissible_two_sided_translate hα (admissible_two_sided_translate hα hf (ha t ht) (hb t ht)) hS1i hS2) D.haarG
    simpa only [hsgs] using this
  have ms1 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ t ∈ s,
      AEStronglyMeasurable (fun g : Mt k r => f (a t * Matrix.of g * b t)) D.μG := by
    intro f c hf t ht
    exact admissible_ae_strongly_measurable (admissible_two_sided_translate hα hf (ha t ht) (hb t ht)) D.haarG

  have b2 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ g : Mt k r,
      (Matrix.of g : Mat k r) ∈ GV k r → ∀ t ∈ s,
      ‖f (a t * sgs p (Matrix.of g) * b t)‖ ≤ c * P * M * gN (Matrix.of g : Mat k r) ^ (-α) := by
    intro f c hf g hg t ht
    rw [hsgs, hPd, hMd]
    exact translated_norm_bound hα hf (ha t ht) (hb t ht) hS1i hS2 hg (hKa t ht) (hKb t ht)
  have b1 : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ}, admitted α c f → ∀ g : Mt k r,
      (Matrix.of g : Mat k r) ∈ GV k r → ∀ t ∈ s,
      ‖f (a t * Matrix.of g * b t)‖ ≤ c * P * 1 * gN (Matrix.of g : Mat k r) ^ (-α) := by
    intro f c hf g hg t ht
    rw [hPd, mul_one]
    exact norm_admissible_of_double_translate_le hα hf (ha t ht) (hb t ht) hg (hKa t ht) (hKb t ht)
  have hm0 : ∀ g : Mt k r, 0 ≤ gN (Matrix.of g : Mat k r) ^ (-α) := fun g => Real.rpow_nonneg (gN_nonneg _) _
  have key := parametric_derivative_under_integral (μ := D.μG) (Sd D p) (Sd_norm_le D hp)
    (u := fun t g => A (a t * sgs p (Matrix.of g) * b t)) (v := fun t g => B (a t * Matrix.of g * b t))
    (u' := fun t g => κ t • A1 (a t * sgs p (Matrix.of g) * b t))
    (v' := fun t g => κ t • B1 (a t * Matrix.of g * b t))
    hs (m := fun g => gN (Matrix.of g : Mat k r) ^ (-α)) (C := (1 + K) * (cA + cB) * P * (1 + M))
    (model_integrable H) (ms2 hA) (ms1 hB) (fun t ht => (ms2 hA1 t ht).const_smul (κ t))
    (fun t ht => (ms1 hB1 t ht).const_smul (κ t))
    (by
      filter_upwards [hG] with g hg t ht
      have hz : sgs p (Matrix.of g) ∈ GV k r := by
        rw [hsgs]; exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hS1i hg) hS2
      exact dA _ hz t ht)
    (by
      filter_upwards [hG] with g hg t ht
      exact dB _ hg t ht)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b2 hA g hg t ht
      have h2 := product_bound_monotone_factors_le (e := 1) (K := K) (c₀ := cA + cB) (M := M) zero_le_one (by linarith) hcA
        (by linarith) hP0 hM0 (by linarith) (hm0 g)
      linarith)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b1 hB g hg t ht
      have h2 := product_bound_monotone_factors_le (e := 1) (K := K) (c₀ := cA + cB) (M := M) zero_le_one (by linarith) hcB
        (by linarith) hP0 zero_le_one (by linarith) (hm0 g)
      linarith)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b2 hA1 g hg t ht
      have h2 := product_bound_monotone_factors_le (e := |κ t|) (K := K) (c₀ := cA + cB) (M := M) (abs_nonneg _)
        (by have := hκ t ht; linarith) hcA (by linarith) hP0 hM0 (by linarith) (hm0 g)
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_left h (abs_nonneg _)) h2)
    (by
      filter_upwards [hG] with g hg t ht
      have h := b1 hB1 g hg t ht
      have h2 := product_bound_monotone_factors_le (e := |κ t|) (K := K) (c₀ := cA + cB) (M := M) (abs_nonneg _)
        (by have := hκ t ht; linarith) hcB (by linarith) hP0 zero_le_one (by linarith) (hm0 g)
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_left h (abs_nonneg _)) h2)
  have i1 := ph_integrable H (admissible_two_sided_translate hα hA1 (ha t₀ ht₀) (hb t₀ ht₀))
    (admissible_two_sided_translate hα hB (ha t₀ ht₀) (hb t₀ ht₀)) hp
  have i2 := ph_integrable H (admissible_two_sided_translate hα hA (ha t₀ ht₀) (hb t₀ ht₀))
    (admissible_two_sided_translate hα hB1 (ha t₀ ht₀) (hb t₀ ht₀)) hp
  have e1 : (∫ g : Mt k r, (hsInner (Sd D p (κ t₀ • A1 (a t₀ * sgs p (Matrix.of g) * b t₀)))
        (B (a t₀ * Matrix.of g * b t₀)) +
      hsInner (Sd D p (A (a t₀ * sgs p (Matrix.of g) * b t₀))) (κ t₀ • B1 (a t₀ * Matrix.of g * b t₀))) ∂D.μG) =
      (κ t₀ : ℂ) * (Ph D (fun g => A1 (a t₀ * g * b t₀)) (fun g => B (a t₀ * g * b t₀)) p +
        Ph D (fun g => A (a t₀ * g * b t₀)) (fun g => B1 (a t₀ * g * b t₀)) p) := by
    unfold Ph
    rw [← integral_add i1 i2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [rho_eq]
    rw [← Complex.coe_smul (κ t₀) (A1 _), ← Complex.coe_smul (κ t₀) (B1 _), map_smul, hsInner_smul_left,
      hsInner_smul_right, Complex.conj_ofReal]
    ring
  rw [← e1]
  have e2 : (fun t => Ph D (fun g => A (a t * g * b t)) (fun g => B (a t * g * b t)) p) =
      fun t => ∫ g : Mt k r, hsInner (Sd D p (A (a t * sgs p (Matrix.of g) * b t)))
        (B (a t * Matrix.of g * b t)) ∂D.μG := by
    funext t
    unfold Ph
    simp only [rho_eq]
  rw [e2]
  exact key

theorem ph_hasDerivAt_y (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hA' : admitted α cA (Rr A)) (hB : admitted α cB B) (hB' : admitted α cB (Rr B)) (dA : DR A) (dB : DR B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => Ph D A B (dilation₂ (x, y') p))
      (((-(rr r / y) : ℝ) : ℂ) * (Ph D (Rr A) B (dilation₂ (x, y) p) + Ph D A (Rr B) (dilation₂ (x, y) p))) y := by
  obtain ⟨K1, hK1, hK1b⟩ := aDil_gN_bound k r (a := y / 2) (b := 2 * y) (by linarith)
  have hs : Set.Ioo (y / 2) (2 * y) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Set.Ioo (y / 2) (2 * y), 0 < t := fun t ht => by have := ht.1; linarith
  have hr := rr_pos r
  have hd : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)}, DR f → ∀ z ∈ GV k r, ∀ t ∈ Set.Ioo (y / 2) (2 * y),
      HasDerivAt (fun t => f (aDil k r x * z * (aDil k r t)⁻¹))
        ((-(rr r / t)) • Rr f (aDil k r x * z * (aDil k r t)⁻¹)) t := by
    intro f df z hz t ht
    exact curveR f (aDil k r x * z) (hpos t ht)
      (df _ (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (aDil_mem k r hx) hz) (aDil_inv_mem k r (hpos t ht))))
  have key := pairing_derivative_locally_dominated H hA hA' hB hB' hp (a := fun _ => aDil k r x) (b := fun t => (aDil k r t)⁻¹)
    (κ := fun t => -(rr r / t)) hs (K := K1 + gN (aDil k r x)⁻¹ + 2 * rr r / y)
    (fun t _ => aDil_mem k r hx) (fun t ht => aDil_inv_mem k r (hpos t ht))
    (fun t _ => by
      have h1 : 0 ≤ 2 * rr r / y := by positivity
      linarith)
    (fun t ht => by
      have h1 : 0 ≤ 2 * rr r / y := by positivity
      have h2 := gN_nonneg (aDil k r x)⁻¹
      have h3 := (hK1b t ⟨ht.1.le, ht.2.le⟩).1
      rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh (aDil_mem k r (hpos t ht)))]
      linarith)
    (fun t ht => by
      have h2 := gN_nonneg (aDil k r x)⁻¹
      have h3 : |-(rr r / t)| ≤ 2 * rr r / y := by
        rw [abs_neg, abs_of_pos (div_pos hr (hpos t ht)), div_le_div_iff₀ (hpos t ht) hy]
        have := ht.1
        nlinarith
      linarith)
    (hd dA) (hd dB)
  rw [ph_dil H (Rr A) B hp hx hy, ph_dil H A (Rr B) hp hx hy]
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact ph_dil H A B hp hx (hpos t ht)

theorem phase_dilation_deriv_x (H : Hyp D Ξ α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hA' : admitted α cA (Ll A)) (hB : admitted α cB B) (hB' : admitted α cB (Ll B)) (dA : DL A) (dB : DL B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => Ph D A B (dilation₂ (x', y) p))
      (((-(rr r / x) : ℝ) : ℂ) * (Ph D (Ll A) B (dilation₂ (x, y) p) + Ph D A (Ll B) (dilation₂ (x, y) p))) x := by
  obtain ⟨K1, hK1, hK1b⟩ := aDil_gN_bound k r (a := x / 2) (b := 2 * x) (by linarith)
  have hs : Set.Ioo (x / 2) (2 * x) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Set.Ioo (x / 2) (2 * x), 0 < t := fun t ht => by have := ht.1; linarith
  have hr := rr_pos r
  have hd : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)}, DL f → ∀ z ∈ GV k r, ∀ t ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun t => f (aDil k r t * z * (aDil k r y)⁻¹))
        ((-(rr r / t)) • Ll f (aDil k r t * z * (aDil k r y)⁻¹)) t := by
    intro f df z hz t ht
    have h := curveL f (z * (aDil k r y)⁻¹) (hpos t ht)
      (df _ (WeylGroupFacts.uh_mul (aDil_mem k r (hpos t ht)) (WeylGroupFacts.uh_mul hz (aDil_inv_mem k r hy))))
    simpa only [Matrix.mul_assoc] using h
  have key := pairing_derivative_locally_dominated H hA hA' hB hB' hp (a := fun t => aDil k r t) (b := fun _ => (aDil k r y)⁻¹)
    (κ := fun t => -(rr r / t)) hs (K := K1 + gN ((aDil k r y)⁻¹)⁻¹ + 2 * rr r / x)
    (fun t ht => aDil_mem k r (hpos t ht)) (fun t _ => aDil_inv_mem k r hy)
    (fun t ht => by
      have h1 : 0 ≤ 2 * rr r / x := by positivity
      have h2 := gN_nonneg ((aDil k r y)⁻¹)⁻¹
      have h3 := (hK1b t ⟨ht.1.le, ht.2.le⟩).2
      linarith)
    (fun t _ => by
      have h1 : 0 ≤ 2 * rr r / x := by positivity
      linarith)
    (fun t ht => by
      have h2 := gN_nonneg ((aDil k r y)⁻¹)⁻¹
      have h3 : |-(rr r / t)| ≤ 2 * rr r / x := by
        rw [abs_neg, abs_of_pos (div_pos hr (hpos t ht)), div_le_div_iff₀ (hpos t ht) hx]
        have := ht.1
        nlinarith
      linarith)
    (hd dA) (hd dB)
  rw [ph_dil H (Ll A) B hp hx hy, ph_dil H A (Ll B) hp hx hy]
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact ph_dil H A B hp (hpos t ht) hy

end phd

section abs

theorem iterated_deriv_two_of_chain {f f1 f2 : ℝ → ℂ} (h0 : ∀ t, HasDerivAt f (f1 t) t) (h1 : ∀ t, HasDerivAt f1 (f2 t) t) :
    iteratedDeriv 2 f = f2 := by
  have e1 : deriv f = f1 := funext fun t => (h0 t).deriv
  have e2 : deriv f1 = f2 := funext fun t => (h1 t).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, e1, e2]

theorem contDiff_two_of_derivatives {f f1 f2 : ℝ → ℂ} (h0 : ∀ t, HasDerivAt f (f1 t) t) (h1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hc : Continuous f2) : ContDiff ℝ 2 f := by
  have e1 : deriv f = f1 := funext fun t => (h0 t).deriv
  have e2 : deriv f1 = f2 := funext fun t => (h1 t).deriv
  have c1 : ContDiff ℝ 1 f1 := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun t => (h1 t).differentiableAt, by rw [e2]; exact hc⟩
  have : ContDiff ℝ (1 + 1) f := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun t => (h0 t).differentiableAt, by simp, by rw [e1]; exact c1⟩
  simpa [one_add_one_eq_two] using this

theorem cutoff_eventually_zero_outside {W : ℝ → ℝ} (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) {t : ℝ} (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2) :
    W =ᶠ[𝓝 t] 0 :=
  notMem_tsupport_iff_eventuallyEq.1 fun h => ht (hWs h)

theorem cutoff_zero_outside {W : ℝ → ℝ} (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) {t : ℝ} (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2) :
    W t = 0 := (cutoff_eventually_zero_outside hWs ht).eq_of_nhds

theorem cutoff_derivative_zero_outside {W : ℝ → ℝ} (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) {t : ℝ} (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2) :
    deriv W t = 0 := by
  rw [(cutoff_eventually_zero_outside hWs ht).deriv_eq]; simp

theorem iteratedDeriv_two_eq_zero_off_support {W : ℝ → ℝ} (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) {t : ℝ} (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2) :
    iteratedDeriv 2 W t = 0 := by
  rw [(cutoff_eventually_zero_outside hWs ht).iteratedDeriv_eq 2]; simp

theorem gam_zero {W : ℝ → ℝ} (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) (ρ : ℝ) (m : ℕ) {t : ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2) : gam ρ W m t = 0 := by
  match m with
  | 0 => simp [gam, cutoff_zero_outside hWs ht, iteratedDeriv_two_eq_zero_off_support hWs ht]
  | 1 => simp [gam, cutoff_zero_outside hWs ht, cutoff_derivative_zero_outside hWs ht]
  | (n + 2) => simp [gam, cutoff_zero_outside hWs ht]

theorem cutoff_div_pow_continuous {v : ℝ → ℝ} (hv : Continuous v) (h0 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v t = 0) (n : ℕ) :
    Continuous (fun t => v t / t ^ n) := by
  have e : (fun t => v t / t ^ n) = fun t => v t / (max t (1 / 2)) ^ n := by
    funext t
    by_cases ht : (1 / 2 : ℝ) ≤ t
    · rw [max_eq_left ht]
    · rw [h0 t (fun h => ht h.1.le)]; simp
  rw [e]
  refine hv.div ((continuous_id.max continuous_const).pow n) fun t => ?_
  have : (0 : ℝ) < max t (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  positivity

theorem gam_continuous {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) (ρ : ℝ) (m : ℕ) : Continuous (gam ρ W m) := by
  have c0 : Continuous W := hW.continuous
  have c1 : Continuous (deriv W) := hW.continuous_deriv (by simp)
  have c2 : Continuous (iteratedDeriv 2 W) := (contDiff_infty.1 hW 2).continuous_iteratedDeriv 2 le_rfl
  have d0 := cutoff_div_pow_continuous c0 (fun t ht => cutoff_zero_outside hWs ht) 2
  have d1 := cutoff_div_pow_continuous c1 (fun t ht => cutoff_derivative_zero_outside hWs ht) 1
  match m with
  | 0 => exact c0.sub c2
  | 1 =>
    have : gam ρ W 1 = fun t => 2 * ρ * (deriv W t / t ^ 1) - ρ * (W t / t ^ 2) := by
      funext t; simp only [gam, pow_one]; ring
    rw [this]
    exact (continuous_const.mul d1).sub (continuous_const.mul d0)
  | (n + 2) =>
    have : gam ρ W (n + 2) = fun t => -(ρ ^ 2 * (W t / t ^ 2)) := by
      funext t; simp only [gam]; ring
    rw [this]
    exact (continuous_const.mul d0).neg

theorem gam_bound {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) (ρ : ℝ) : ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ m t, |gam ρ W m t| ≤ Γ := by
  have hb : ∀ m, ∃ C, ∀ t, ‖gam ρ W m t‖ ≤ C := fun m =>
    (gam_continuous hW hWs ρ m).bounded_above_of_compact_support
      (HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2))
        fun t ht => gam_zero hWs ρ m fun h => ht ⟨h.1.le, h.2.le⟩)
  obtain ⟨C0, h0⟩ := hb 0
  obtain ⟨C1, h1⟩ := hb 1
  obtain ⟨C2, h2⟩ := hb 2
  refine ⟨max (max C0 C1) C2, ?_, ?_⟩
  · exact le_trans (le_trans (norm_nonneg _) (h2 0)) (le_max_right _ _)
  · intro m t
    match m with
    | 0 => exact le_trans (h0 t) (le_trans (le_max_left _ _) (le_max_left _ _))
    | 1 => exact le_trans (h1 t) (le_trans (le_max_right _ _) (le_max_left _ _))
    | (n + 2) => exact le_trans (h2 t) (le_max_right _ _)

theorem oneMinusDD_add {h₁ h₂ : ℝ → ℝ → ℂ} (a₁ : ∀ x, ContDiff ℝ 2 (fun y => h₁ x y))
    (a₂ : ∀ x, ContDiff ℝ 2 (fun y => h₂ x y))
    (b₁ : ∀ y, ContDiff ℝ 2 (fun x => h₁ x y - iteratedDeriv 2 (fun y' => h₁ x y') y))
    (b₂ : ∀ y, ContDiff ℝ 2 (fun x => h₂ x y - iteratedDeriv 2 (fun y' => h₂ x y') y)) (x y : ℝ) :
    oneMinusDD (fun x y => h₁ x y + h₂ x y) x y = oneMinusDD h₁ x y + oneMinusDD h₂ x y := by
  have i1 : ∀ x y, iteratedDeriv 2 (fun y' => h₁ x y' + h₂ x y') y =
      iteratedDeriv 2 (fun y' => h₁ x y') y + iteratedDeriv 2 (fun y' => h₂ x y') y := fun x y =>
    iteratedDeriv_fun_add (a₁ x).contDiffAt (a₂ x).contDiffAt
  have i2 : (fun x => (h₁ x y + h₂ x y) - iteratedDeriv 2 (fun y' => h₁ x y' + h₂ x y') y) =
      fun x => (h₁ x y - iteratedDeriv 2 (fun y' => h₁ x y') y) +
        (h₂ x y - iteratedDeriv 2 (fun y' => h₂ x y') y) := by
    funext x; rw [i1]; ring
  unfold oneMinusDD
  simp only []
  rw [i2, i1, iteratedDeriv_fun_add (b₁ y).contDiffAt (b₂ y).contDiffAt]
  ring

theorem oneMinusDD_const_mul (a : ℂ) (h : ℝ → ℝ → ℂ) (x y : ℝ) :
    oneMinusDD (fun x y => a * h x y) x y = a * oneMinusDD h x y := by
  have i2 : (fun x => a * h x y - iteratedDeriv 2 (fun y' => a * h x y') y) =
      fun x => a * (h x y - iteratedDeriv 2 (fun y' => h x y') y) := by
    funext x; rw [iteratedDeriv_const_mul_field]; ring
  unfold oneMinusDD
  simp only []
  rw [i2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  ring

theorem cutoff_product_rule {u u' : ℝ → ℝ} (hu : ∀ t, HasDerivAt u (u' t) t) (hu0 : ∀ t, t ≤ 0 → u =ᶠ[𝓝 t] 0)
    {q q' : ℝ → ℂ} (hq : ∀ t, 0 < t → HasDerivAt q (q' t) t) (t : ℝ) :
    HasDerivAt (fun t => (u t : ℂ) * q t) ((u' t : ℂ) * q t + (u t : ℂ) * q' t) t := by
  by_cases ht : 0 < t
  · exact (hu t).ofReal_comp.mul (hq t ht)
  · have h0 := hu0 t (not_lt.1 ht)
    have e0 : u t = 0 := h0.eq_of_nhds
    have e1 : u' t = 0 := by
      have := (hu t).deriv
      rw [h0.deriv_eq] at this
      simpa using this.symm
    rw [e0, e1]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    refine (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [h0] with s hs
    simp [hs]

theorem cutoff_mul_continuous {v : ℝ → ℝ} (hv : Continuous v) (h0 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v t = 0) {q : ℝ → ℂ}
    (hq : ContinuousOn q (Set.Ioi 0)) : Continuous (fun t => (v t : ℂ) * q t) := by
  have e : (fun t => (v t : ℂ) * q t) = fun t => (v t : ℂ) * q (max t (1 / 2)) := by
    funext t
    by_cases ht : (1 / 2 : ℝ) ≤ t
    · rw [max_eq_left ht]
    · rw [h0 t (fun h => ht h.1.le)]; simp
  rw [e]
  refine (Complex.continuous_ofReal.comp hv).mul
    (hq.comp_continuous (continuous_id.max continuous_const) fun t => ?_)
  show (0 : ℝ) < max t (1 / 2)
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)

theorem nonpositive_not_in_interval {t : ℝ} (ht : t ≤ 0) : t ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h => by
  have := h.1; linarith

theorem regularised_product_second_derivative {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) {q0 q1 q2 : ℝ → ℂ}
    (h0 : ∀ t, 0 < t → HasDerivAt q0 (((-(ρ / t) : ℝ) : ℂ) * q1 t) t)
    (h1 : ∀ t, 0 < t → HasDerivAt q1 (((-(ρ / t) : ℝ) : ℂ) * q2 t) t)
    (hc : ContinuousOn q2 (Set.Ioi 0)) :
    ContDiff ℝ 2 (fun t => (W t : ℂ) * q0 t) ∧
    ∀ t, (W t : ℂ) * q0 t - iteratedDeriv 2 (fun t => (W t : ℂ) * q0 t) t =
      (gam ρ W 0 t : ℂ) * q0 t + (gam ρ W 1 t : ℂ) * q1 t + (gam ρ W 2 t : ℂ) * q2 t := by
  have hW2 : ContDiff ℝ 2 W := contDiff_infty.1 hW 2
  have dW : ∀ t, HasDerivAt W (deriv W t) t := fun t =>
    (hW2.differentiable (by norm_num) t).hasDerivAt
  have hdW1 : ContDiff ℝ 1 (deriv W) := by
    have : ContDiff ℝ (1 + 1) W := by simpa [one_add_one_eq_two] using hW2
    exact (contDiff_succ_iff_deriv.1 this).2.2
  have ddW : ∀ t, HasDerivAt (deriv W) (iteratedDeriv 2 W t) t := fun t => by
    have := (hdW1.differentiable (by norm_num) t).hasDerivAt
    rwa [iteratedDeriv_succ, iteratedDeriv_one]
  have evW : ∀ t, t ≤ 0 → W =ᶠ[𝓝 t] 0 := fun t ht => cutoff_eventually_zero_outside hWs (nonpositive_not_in_interval ht)
  have evdW : ∀ t, t ≤ 0 → deriv W =ᶠ[𝓝 t] 0 := fun t ht => by
    have := (evW t ht).deriv
    refine this.trans ?_
    exact Filter.Eventually.of_forall fun s => by simp
  have evu2 : ∀ t, t ≤ 0 → (fun t => -(ρ * (W t / t))) =ᶠ[𝓝 t] 0 := fun t ht => by
    filter_upwards [evW t ht] with s hs
    simp [hs]
  have du2 : ∀ t, HasDerivAt (fun t => -(ρ * (W t / t))) (-(ρ * (deriv W t / t - W t / t ^ 2))) t := fun t => by
    by_cases ht : t = 0
    · have e : -(ρ * (deriv W t / t - W t / t ^ 2)) = 0 := by
        simp [cutoff_zero_outside hWs (nonpositive_not_in_interval ht.le), cutoff_derivative_zero_outside hWs (nonpositive_not_in_interval ht.le)]
      rw [e]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (evu2 t ht.le)
    · have := (((dW t).div (hasDerivAt_id t) ht).const_mul ρ).neg
      refine HasDerivAt.congr_deriv (f := fun t => -(ρ * (W t / t))) this ?_
      simp only [id]
      field_simp
  have A : ∀ t, HasDerivAt (fun t => (W t : ℂ) * q0 t)
      (((deriv W t : ℝ) : ℂ) * q0 t + ((-(ρ * (W t / t)) : ℝ) : ℂ) * q1 t) t := fun t => by
    convert cutoff_product_rule dW evW h0 t using 1
    push_cast; ring
  have B : ∀ t, HasDerivAt (fun t => ((deriv W t : ℝ) : ℂ) * q0 t + ((-(ρ * (W t / t)) : ℝ) : ℂ) * q1 t)
      (((W t - gam ρ W 0 t : ℝ) : ℂ) * q0 t - (gam ρ W 1 t : ℂ) * q1 t - (gam ρ W 2 t : ℂ) * q2 t) t :=
    fun t => by
    refine ((cutoff_product_rule ddW evdW h0 t).add (cutoff_product_rule du2 evu2 h1 t)).congr_deriv ?_
    simp only [gam]; push_cast; ring
  have cq0 : ContinuousOn q0 (Set.Ioi 0) := fun t ht => (h0 t ht).continuousAt.continuousWithinAt
  have cq1 : ContinuousOn q1 (Set.Ioi 0) := fun t ht => (h1 t ht).continuousAt.continuousWithinAt
  have C : Continuous fun t => ((W t - gam ρ W 0 t : ℝ) : ℂ) * q0 t - (gam ρ W 1 t : ℂ) * q1 t -
      (gam ρ W 2 t : ℂ) * q2 t := by
    refine ((cutoff_mul_continuous (hW.continuous.sub (gam_continuous hW hWs ρ 0)) (fun t ht => ?_) cq0).sub
      (cutoff_mul_continuous (gam_continuous hW hWs ρ 1) (fun t ht => gam_zero hWs ρ 1 ht) cq1)).sub
      (cutoff_mul_continuous (gam_continuous hW hWs ρ 2) (fun t ht => gam_zero hWs ρ 2 ht) hc)
    show W t - gam ρ W 0 t = 0
    rw [cutoff_zero_outside hWs ht, gam_zero hWs ρ 0 ht, sub_zero]
  refine ⟨contDiff_two_of_derivatives A B C, fun t => ?_⟩
  rw [iterated_deriv_two_of_chain A B]
  push_cast; ring

theorem cutoff_product_continuous {v1 v2 : ℝ → ℝ} (hv1 : Continuous v1) (hv2 : Continuous v2)
    (h1 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v1 t = 0) (h2 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v2 t = 0)
    {q : ℝ → ℝ → ℂ} (hq : ContinuousOn (fun t : ℝ × ℝ => q t.1 t.2) Quad) :
    Continuous (fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2) := by
  have e : (fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2) =
      fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q (max t.1 (1 / 2)) (max t.2 (1 / 2)) := by
    funext t
    by_cases ht1 : (1 / 2 : ℝ) ≤ t.1
    · by_cases ht2 : (1 / 2 : ℝ) ≤ t.2
      · rw [max_eq_left ht1, max_eq_left ht2]
      · rw [h2 t.2 (fun h => ht2 h.1.le)]; simp
    · rw [h1 t.1 (fun h => ht1 h.1.le)]; simp
  rw [e]
  have hc : Continuous fun t : ℝ × ℝ => ((max t.1 (1 / 2), max t.2 (1 / 2)) : ℝ × ℝ) :=
    (continuous_fst.max continuous_const).prodMk (continuous_snd.max continuous_const)
  have hm : ∀ t : ℝ × ℝ, ((max t.1 (1 / 2), max t.2 (1 / 2)) : ℝ × ℝ) ∈ Quad := fun t =>
    ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _),
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)⟩
  exact (Complex.continuous_ofReal.comp ((hv1.comp continuous_fst).mul (hv2.comp continuous_snd))).mul
    (hq.comp_continuous hc hm)

theorem cutoff_product_integrable {v1 v2 : ℝ → ℝ} (hv1 : Continuous v1) (hv2 : Continuous v2)
    (h1 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v1 t = 0) (h2 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v2 t = 0)
    {q : ℝ → ℝ → ℂ} (hq : ContinuousOn (fun t : ℝ × ℝ => q t.1 t.2) Quad) {E : ℝ × ℝ → ℂ} (hE : Continuous E) :
    Integrable (fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2 * E t) := by
  refine ((cutoff_product_continuous hv1 hv2 h1 h2 hq).mul hE).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).prod (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2))) fun t ht => ?_
  show ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2 * E t = 0
  by_cases a1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
  · by_cases a2 : t.2 ∈ Set.Ioo (1 / 2 : ℝ) 2
    · exact absurd ⟨⟨a1.1.le, a1.2.le⟩, ⟨a2.1.le, a2.2.le⟩⟩ ht
    · rw [h2 t.2 a2]; simp
  · rw [h1 t.1 a1]; simp

theorem exp_sum_split (x₁ x₂ a b : ℝ) :
    Complex.exp (Complex.I * ((x₁ * a + x₂ * b : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((x₁ * a : ℝ) : ℂ)) * Complex.exp (Complex.I * ((x₂ * b : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem continuous_exp_I_linear_form (x₁ x₂ : ℝ) :
    Continuous fun t : ℝ × ℝ => Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
  fun_prop

theorem fourier_slice_in_x {K K' : ℝ → ℝ → ℂ} (x₁ x₂ : ℝ) (c : ℂ)
    (hK : Integrable fun t : ℝ × ℝ => K t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)))
    (hK' : Integrable fun t : ℝ × ℝ => K' t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)))
    (h : ∀ y, (∫ x, K x y * Complex.exp (Complex.I * ((x₁ * x : ℝ) : ℂ))) =
      c * ∫ x, K' x y * Complex.exp (Complex.I * ((x₁ * x : ℝ) : ℂ))) :
    (∫ t : ℝ × ℝ, K t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      c * ∫ t : ℝ × ℝ, K' t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
  have key : ∀ (L : ℝ → ℝ → ℂ) (y : ℝ),
      (∫ x, L x y * Complex.exp (Complex.I * ((x₁ * x + x₂ * y : ℝ) : ℂ))) =
        (∫ x, L x y * Complex.exp (Complex.I * ((x₁ * x : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((x₂ * y : ℝ) : ℂ)) := fun L y => by
    rw [← integral_mul_const]
    congr 1; funext x; rw [exp_sum_split]; ring
  rw [Measure.volume_eq_prod, integral_prod_symm _ hK, integral_prod_symm _ hK', ← integral_const_mul]
  congr 1; funext y
  simp only []
  rw [key K y, key K' y, h y]; ring

theorem integral_slice_second_variable_eq {K K' : ℝ → ℝ → ℂ} (x₁ x₂ : ℝ) (c : ℂ)
    (hK : Integrable fun t : ℝ × ℝ => K t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)))
    (hK' : Integrable fun t : ℝ × ℝ => K' t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)))
    (h : ∀ x, (∫ y, K x y * Complex.exp (Complex.I * ((x₂ * y : ℝ) : ℂ))) =
      c * ∫ y, K' x y * Complex.exp (Complex.I * ((x₂ * y : ℝ) : ℂ))) :
    (∫ t : ℝ × ℝ, K t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      c * ∫ t : ℝ × ℝ, K' t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
  have key : ∀ (L : ℝ → ℝ → ℂ) (x : ℝ),
      (∫ y, L x y * Complex.exp (Complex.I * ((x₁ * x + x₂ * y : ℝ) : ℂ))) =
        (∫ y, L x y * Complex.exp (Complex.I * ((x₂ * y : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((x₁ * x : ℝ) : ℂ)) := fun L x => by
    rw [← integral_mul_const]
    congr 1; funext y; rw [exp_sum_split]; ring
  rw [Measure.volume_eq_prod, integral_prod _ hK, integral_prod _ hK', ← integral_const_mul]
  congr 1; funext x
  simp only []
  rw [key K x, key K' x, h x]; ring

def regularised_kernel_product (ρ : ℝ) (W : ℝ → ℝ) (q : ℕ → ℕ → ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (W x : ℂ) * ((gam ρ W 0 y : ℂ) * q 0 0 x y + (gam ρ W 1 y : ℂ) * q 0 1 x y + (gam ρ W 2 y : ℂ) * q 0 2 x y)

theorem second_derivative_in_y {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) (q : ℕ → ℕ → ℝ → ℝ → ℂ)
    (hy : ∀ l < 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun y' => q 0 l x y') (((-(ρ / y) : ℝ) : ℂ) * q 0 (l + 1) x y) y)
    (hc : ∀ m ≤ 2, ∀ l ≤ 2, ContinuousOn (fun t : ℝ × ℝ => q m l t.1 t.2) Quad)
    (h : ℝ → ℝ → ℂ) (hh : ∀ x y, h x y = ((W x * W y : ℝ) : ℂ) * q 0 0 x y) (x : ℝ) :
    ContDiff ℝ 2 (fun y => h x y) ∧
      ∀ y, h x y - iteratedDeriv 2 (fun y' => h x y') y = regularised_kernel_product ρ W q x y := by
  have e : (fun y => h x y) = fun y => (W x : ℂ) * ((W y : ℂ) * q 0 0 x y) := by
    funext y; rw [hh]; push_cast; ring
  have e' : ∀ y, h x y = (W x : ℂ) * ((W y : ℂ) * q 0 0 x y) := fun y => congrFun e y
  by_cases hx0 : 0 < x
  · have cq : ContinuousOn (q 0 2 x) (Set.Ioi 0) :=
      (hc 0 (by norm_num) 2 le_rfl).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun y hy0 => ⟨hx0, hy0⟩)
    obtain ⟨cd, fm⟩ := regularised_product_second_derivative hW hWs ρ (q0 := q 0 0 x) (q1 := q 0 1 x) (q2 := q 0 2 x)
      (fun t ht => hy 0 (by norm_num) x hx0 t ht) (fun t ht => hy 1 (by norm_num) x hx0 t ht) cq
    refine ⟨by rw [e]; exact contDiff_const.mul cd, fun y => ?_⟩
    rw [e, e' y, iteratedDeriv_const_mul_field, ← mul_sub, fm y]
    rfl
  · have hW0 : W x = 0 := cutoff_zero_outside hWs (nonpositive_not_in_interval (not_lt.1 hx0))
    refine ⟨?_, fun y => ?_⟩
    · rw [e, hW0]; simp only [Complex.ofReal_zero, zero_mul]; exact contDiff_const
    · rw [e, e' y, iteratedDeriv_const_mul_field, hW0]; simp [regularised_kernel_product, hW0]

theorem contDiff_two_outer_kernel {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) (q : ℕ → ℕ → ℝ → ℝ → ℂ)
    (hx : ∀ m < 2, ∀ l ≤ 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun x' => q m l x' y) (((-(ρ / x) : ℝ) : ℂ) * q (m + 1) l x y) x)
    (hc : ∀ m ≤ 2, ∀ l ≤ 2, ContinuousOn (fun t : ℝ × ℝ => q m l t.1 t.2) Quad) (y : ℝ) :
    ContDiff ℝ 2 (fun x => regularised_kernel_product ρ W q x y) ∧
      ∀ x, regularised_kernel_product ρ W q x y - iteratedDeriv 2 (fun x' => regularised_kernel_product ρ W q x' y) x =
        ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3, ((gam ρ W m x * gam ρ W l y : ℝ) : ℂ) * q m l x y := by
  by_cases hy0 : 0 < y
  · have cq : ∀ l ≤ 2, ContinuousOn (fun x => q 2 l x y) (Set.Ioi 0) := fun l hl =>
      (hc 2 le_rfl l hl).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx0 => ⟨hx0, hy0⟩)
    have hd : ∀ m < 2, ∀ t, 0 < t → HasDerivAt
        (fun x => (gam ρ W 0 y : ℂ) * q m 0 x y + (gam ρ W 1 y : ℂ) * q m 1 x y + (gam ρ W 2 y : ℂ) * q m 2 x y)
        (((-(ρ / t) : ℝ) : ℂ) * ((gam ρ W 0 y : ℂ) * q (m + 1) 0 t y + (gam ρ W 1 y : ℂ) * q (m + 1) 1 t y +
          (gam ρ W 2 y : ℂ) * q (m + 1) 2 t y)) t := fun m hm t ht => by
      refine ((((hx m hm 0 (by norm_num) t ht y hy0).const_mul (gam ρ W 0 y : ℂ)).add
        ((hx m hm 1 (by norm_num) t ht y hy0).const_mul (gam ρ W 1 y : ℂ))).add
        ((hx m hm 2 le_rfl t ht y hy0).const_mul (gam ρ W 2 y : ℂ))).congr_deriv ?_
      ring
    obtain ⟨cd, fm⟩ := regularised_product_second_derivative hW hWs ρ (hd 0 (by norm_num)) (hd 1 (by norm_num))
      (((continuousOn_const.mul (cq 0 (by norm_num))).add (continuousOn_const.mul (cq 1 (by norm_num)))).add
        (continuousOn_const.mul (cq 2 le_rfl)))
    refine ⟨cd, fun x => ?_⟩
    have := fm x
    unfold regularised_kernel_product
    rw [this]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast; ring
  · have g0 : ∀ l, gam ρ W l y = 0 := fun l => gam_zero hWs ρ l (nonpositive_not_in_interval (not_lt.1 hy0))
    have e : (fun x => regularised_kernel_product ρ W q x y) = fun _ => 0 := by
      funext x; simp [regularised_kernel_product, g0]
    refine ⟨by rw [e]; exact contDiff_const, fun x => ?_⟩
    rw [e]
    simp [regularised_kernel_product, g0]

theorem al2 {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) (q : ℕ → ℕ → ℝ → ℝ → ℂ)
    (hy : ∀ l < 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun y' => q 0 l x y') (((-(ρ / y) : ℝ) : ℂ) * q 0 (l + 1) x y) y)
    (hx : ∀ m < 2, ∀ l ≤ 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun x' => q m l x' y) (((-(ρ / x) : ℝ) : ℂ) * q (m + 1) l x y) x)
    (hc : ∀ m ≤ 2, ∀ l ≤ 2, ContinuousOn (fun t : ℝ × ℝ => q m l t.1 t.2) Quad)
    (h : ℝ → ℝ → ℂ) (hh : ∀ x y, h x y = ((W x * W y : ℝ) : ℂ) * q 0 0 x y) :
    (∀ x y, oneMinusDD h x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam ρ W m x * gam ρ W l y : ℝ) : ℂ) * q m l x y) ∧
    (∀ x, ContDiff ℝ 2 (fun y => h x y)) ∧
    (∀ y, ContDiff ℝ 2 (fun x => h x y - iteratedDeriv 2 (fun y' => h x y') y)) ∧
    (∀ x₁ x₂ : ℝ, (∫ t : ℝ × ℝ, oneMinusDD h t.1 t.2 *
        Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      (((1 + x₁ ^ 2) * (1 + x₂ ^ 2) : ℝ) : ℂ) *
        ∫ t : ℝ × ℝ, h t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) := by
  have IN := second_derivative_in_y hW hWs ρ q hy hc h hh
  have OUT := contDiff_two_outer_kernel hW hWs ρ q hx hc
  have ek : ∀ y, (fun x => h x y - iteratedDeriv 2 (fun y' => h x y') y) = fun x => regularised_kernel_product ρ W q x y :=
    fun y => funext fun x => (IN x).2 y
  have om_eq : ∀ x y, oneMinusDD h x y =
      regularised_kernel_product ρ W q x y - iteratedDeriv 2 (fun x' => regularised_kernel_product ρ W q x' y) x := fun x y => by
    unfold oneMinusDD
    rw [ek y, (IN x).2 y]
  have form : ∀ x y, oneMinusDD h x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam ρ W m x * gam ρ W l y : ℝ) : ℂ) * q m l x y := fun x y => by
    rw [om_eq]; exact (OUT y).2 x
  refine ⟨form, fun x => (IN x).1, fun y => by rw [ek y]; exact (OUT y).1, fun x₁ x₂ => ?_⟩
  have cW : Continuous W := hW.continuous
  have zW : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → W t = 0 := fun t ht => cutoff_zero_outside hWs ht
  have cg := gam_continuous hW hWs ρ
  have zg : ∀ m t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → gam ρ W m t = 0 := fun m t ht => gam_zero hWs ρ m ht
  have hE := continuous_exp_I_linear_form x₁ x₂
  have I_h : Integrable fun t : ℝ × ℝ =>
      h t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
    refine (cutoff_product_integrable cW cW zW zW (hc 0 (by norm_num) 0 (by norm_num)) hE).congr (ae_of_all _ fun t => ?_)
    simp only [hh]
  have I_k : Integrable fun t : ℝ × ℝ =>
      regularised_kernel_product ρ W q t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
    refine (((cutoff_product_integrable cW (cg 0) zW (zg 0) (hc 0 (by norm_num) 0 (by norm_num)) hE).add
      (cutoff_product_integrable cW (cg 1) zW (zg 1) (hc 0 (by norm_num) 1 (by norm_num)) hE)).add
      (cutoff_product_integrable cW (cg 2) zW (zg 2) (hc 0 (by norm_num) 2 le_rfl) hE)).congr (ae_of_all _ fun t => ?_)
    simp only [Pi.add_apply, regularised_kernel_product]; push_cast; ring
  have I_o : Integrable fun t : ℝ × ℝ =>
      oneMinusDD h t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
    have : Integrable fun t : ℝ × ℝ => ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
        ((gam ρ W m t.1 * gam ρ W l t.2 : ℝ) : ℂ) * q m l t.1 t.2 *
          Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) :=
      integrable_finsetSum _ fun m hm => integrable_finsetSum _ fun l hl =>
        cutoff_product_integrable (cg m) (cg l) (zg m) (zg l)
          (hc m (by have := Finset.mem_range.1 hm; omega) l (by have := Finset.mem_range.1 hl; omega)) hE
    refine this.congr (ae_of_all _ fun t => ?_)
    simp only [form, Finset.sum_mul]
  have csk : ∀ y, HasCompactSupport fun x => regularised_kernel_product ρ W q x y := fun y =>
    HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)) fun x hx0 => by
      simp [regularised_kernel_product, zW x fun h => hx0 ⟨h.1.le, h.2.le⟩]
  have csh : ∀ x, HasCompactSupport fun y => h x y := fun x =>
    HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)) fun y hy0 => by
      simp [hh, zW y fun h => hy0 ⟨h.1.le, h.2.le⟩]
  have sX := fourier_slice_in_x (K := oneMinusDD h) (K' := regularised_kernel_product ρ W q) x₁ x₂ ((1 + x₁ ^ 2 : ℝ) : ℂ) I_o I_k
    (fun y => by
      simp only [om_eq]
      exact Formalism.FourierDecayAlt.P.integration_by_parts_regularised (fun x => regularised_kernel_product ρ W q x y) (OUT y).1 (csk y) x₁)
  have sY := integral_slice_second_variable_eq (K := regularised_kernel_product ρ W q) (K' := h) x₁ x₂ ((1 + x₂ ^ 2 : ℝ) : ℂ) I_k I_h
    (fun x => by
      simp only [← (IN x).2]
      exact Formalism.FourierDecayAlt.P.integration_by_parts_regularised (fun y => h x y) (IN x).1 (csh x) x₂)
  rw [sX, sY]; push_cast; ring

end abs

section wd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Wd_contDiff (D : RealPlaceData k r Wp Wq) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Wd D) := by
  unfold Wd
  exact D.χ_smooth.mul (contDiff_id.pow _)

theorem Wd_tsupport (D : RealPlaceData k r Wp Wq) : tsupport (Wd D) ⊆ Set.Ioo (1 / 2) 2 := by
  refine subset_trans ?_ D.χ_supp
  exact tsupport_mul_subset_left

end wd

section shared

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def phase (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) (t : ℝ × ℝ) : ℝ :=
  τ.1 * t.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * t.2 * lam k r D.z' (Matrix.of p.2.2)

def wt (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : ℝ :=
  (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ * (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹

def LL (D : RealPlaceData k r Wp Wq) (p : SS k r) : ℝ :=
  (1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-2 : ℝ) * (1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-2 : ℝ)

def Et (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Set.indicator ({p | D.inSS p} ×ˢ Quad) (fun q => Ef D F F' q.1 q.2) q

def Bt (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Set.indicator ({p | D.inSS p} ×ˢ Quad) (fun q => regBracket D F F' q.1 q.2.1 q.2.2) q

def Gt (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) (p : SS k r) : ℂ :=
  (wt D τ p : ℂ) * ∫ t : ℝ × ℝ, Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem XX_nonneg (Ξ : Mat k r → NNReal) (p : SS k r) : 0 ≤ XX Ξ p := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

theorem LL_nonneg (D : RealPlaceData k r Wp Wq) (p : SS k r) : 0 ≤ LL D p := by unfold LL; positivity

theorem wt_nonneg (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : 0 ≤ wt D τ p := by unfold wt; positivity

theorem lorentzian_weight_bound {τ : ℝ} (h : 0 < τ) (l : ℝ) :
    (1 + τ ^ 2 * l ^ 2)⁻¹ ≤ 2 * max 1 (τ ^ 2)⁻¹ * (1 + |l|) ^ (-2 : ℝ) := by
  have e : (1 + |l|) ^ (-2 : ℝ) = ((1 + |l|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_num
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  have m1 : (1 : ℝ) ≤ max 1 (τ ^ 2)⁻¹ := le_max_left _ _
  have m2 : (τ ^ 2)⁻¹ ≤ max 1 (τ ^ 2)⁻¹ := le_max_right _ _
  have m3 : 1 ≤ max 1 (τ ^ 2)⁻¹ * τ ^ 2 := by
    have : (τ ^ 2)⁻¹ * τ ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    calc (1 : ℝ) = (τ ^ 2)⁻¹ * τ ^ 2 := this.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right m2 (by positivity)
  have hl : l ^ 2 = |l| ^ 2 := (sq_abs l).symm
  rw [hl]
  set a := |l| with ha
  have ha0 : 0 ≤ a := abs_nonneg l
  set M := max 1 (τ ^ 2)⁻¹
  have : (1 + τ ^ 2 * a ^ 2) * (2 * M) = 2 * M + 2 * (M * τ ^ 2) * a ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg (1 - a), mul_le_mul_of_nonneg_right m3 (sq_nonneg a)]

theorem wt_le (D : RealPlaceData k r Wp Wq) {τ : ℝ × ℝ} (h1 : 0 < τ.1) (h2 : 0 < τ.2) (p : SS k r) :
    wt D τ p ≤ 4 * max 1 (τ.1 ^ 2)⁻¹ * max 1 (τ.2 ^ 2)⁻¹ * LL D p := by
  have a1 := lorentzian_weight_bound h1 (lam k r D.z (Matrix.of p.1.2))
  have a2 := lorentzian_weight_bound h2 (lam k r D.z' (Matrix.of p.2.2))
  unfold wt LL
  calc _ ≤ (2 * max 1 (τ.1 ^ 2)⁻¹ * (1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-2 : ℝ)) *
        (2 * max 1 (τ.2 ^ 2)⁻¹ * (1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-2 : ℝ)) :=
        mul_le_mul a1 a2 (by positivity) (by positivity)
    _ = _ := by ring

theorem wt_continuous (D : RealPlaceData k r Wp Wq) : Continuous (fun x : (ℝ × ℝ) × SS k r => wt D x.1 x.2) := by
  unfold wt
  have c1 : Continuous (fun x : (ℝ × ℝ) × SS k r => lam k r D.z (Matrix.of x.2.1.2)) :=
    (lam_continuous k r D.z).comp (continuous_snd.comp (continuous_fst.comp continuous_snd))
  have c2 : Continuous (fun x : (ℝ × ℝ) × SS k r => lam k r D.z' (Matrix.of x.2.2.2)) :=
    (lam_continuous k r D.z').comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  refine Continuous.mul (Continuous.inv₀ (by fun_prop) (fun x => by positivity))
    (Continuous.inv₀ (by fun_prop) (fun x => by positivity))

theorem phase_continuous (D : RealPlaceData k r Wp Wq) :
    Continuous (fun x : ((ℝ × ℝ) × SS k r) × (ℝ × ℝ) => phase D x.1.1 x.1.2 x.2) := by
  unfold phase
  have c1 : Continuous (fun x : ((ℝ × ℝ) × SS k r) × (ℝ × ℝ) => lam k r D.z (Matrix.of x.1.2.1.2)) :=
    (lam_continuous k r D.z).comp
      (continuous_snd.comp (continuous_fst.comp (continuous_snd.comp continuous_fst)))
  have c2 : Continuous (fun x : ((ℝ × ℝ) × SS k r) × (ℝ × ℝ) => lam k r D.z' (Matrix.of x.1.2.2.2)) :=
    (lam_continuous k r D.z').comp
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_fst)))
  fun_prop

theorem weight_integrable_first_factor {Ξ : Mat k r → NNReal} (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r × Mt k r))
    (hm : Measurable fun x : Mt k r => Ξ (Matrix.of x))
    (h : (∫⁻ p : Mt k r × Mt k r, Ξ (Matrix.of p.2 * Matrix.of p.1) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂μ) < ∞) :
    Integrable (fun p : Mt k r × Mt k r => (Ξ (Matrix.of p.2 * Matrix.of p.1) : ℝ) *
      (1 + |lam k r z (Matrix.of p.2)|) ^ (-2 : ℝ)) μ := by
  let mm : Mt k r × Mt k r → Mt k r := fun p => (Matrix.of p.2 * Matrix.of p.1 : Mat k r)
  have cm : Continuous mm := Continuous.matrix_mul continuous_snd continuous_fst
  have m1 : Measurable (fun p : Mt k r × Mt k r => Ξ (Matrix.of p.2 * Matrix.of p.1)) :=
    hm.comp (cm.measurable)
  have c2 : Continuous (fun p : Mt k r × Mt k r => lam k r z (Matrix.of p.2)) :=
    (lam_continuous k r z).comp continuous_snd
  have m2 : Measurable (fun p : Mt k r × Mt k r => (1 + |lam k r z (Matrix.of p.2)|) ^ (-2 : ℝ)) := by
    have : Measurable (fun p : Mt k r × Mt k r => lam k r z (Matrix.of p.2)) := c2.measurable
    fun_prop
  refine ⟨(m1.coe_nnreal_real.mul m2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun p => ?_
  rw [enorm_mul, Real.enorm_eq_ofReal (NNReal.coe_nonneg _), Real.enorm_eq_ofReal (by positivity),
    ENNReal.ofReal_coe_nnreal]

theorem xi_integrable (H : Hyp D Ξ α) : Integrable (fun p : SS k r => XX Ξ p * LL D p) D.μSS := by
  have := haar_sigmaFinite D.haarW
  have := haar_sigmaFinite D.haarN
  have := haar_sigmaFinite D.haarW'
  obtain ⟨hm, h1, h2⟩ := H.xi
  have i1 := weight_integrable_first_factor D.z (D.μW.prod D.μN) hm h1
  have i2 := weight_integrable_first_factor D.z' (D.μW'.prod D.μN) hm h2
  have := i1.mul_prod i2
  refine this.congr (ae_of_all _ fun p => ?_)
  simp only [XX, LL]
  ring

theorem QR_hasDerivAt_y (H : Hyp D Ξ α) {l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA (l + 1) 0 A) (hB : AdmW α cB (l + 1) 0 B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => QR D p 0 l A B x y') (((-(rr r / y) : ℝ) : ℂ) * QR D p 0 (l + 1) A B x y) y := by
  induction l generalizing A B with
  | zero =>
    exact ph_hasDerivAt_y H (hA.1 0 (by omega) 0 le_rfl) (hA.1 1 le_rfl 0 le_rfl) (hB.1 0 (by omega) 0 le_rfl)
      (hB.1 1 le_rfl 0 le_rfl) (hA.2.1 0 (by omega)) (hB.2.1 0 (by omega)) hp hx hy
  | succ l ih =>
    have h1 := ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)
    have h2 := ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3

theorem hasDerivAt_left_derivative_pairing_x (H : Hyp D Ξ α) {m : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA 0 (m + 1) A) (hB : AdmW α cB 0 (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QL D p m A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QL D p (m + 1) A B x y) x := by
  induction m generalizing A B with
  | zero =>
    exact phase_dilation_deriv_x H (hA.1 0 le_rfl 0 (by omega)) (hA.1 0 le_rfl 1 le_rfl) (hB.1 0 le_rfl 0 (by omega))
      (hB.1 0 le_rfl 1 le_rfl) (hA.2.2 0 le_rfl 0 (by omega)) (hB.2.2 0 le_rfl 0 (by omega)) hp hx hy
  | succ m ih =>
    have h1 := ih (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB)
    have h2 := ih (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3

theorem regularised_pairing_deriv_x (H : Hyp D Ξ α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l (m + 1) A) (hB : AdmW α cB l (m + 1) B) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => QR D p m l A B x' y) (((-(rr r / x) : ℝ) : ℂ) * QR D p (m + 1) l A B x y) x := by
  induction l generalizing A B with
  | zero => exact hasDerivAt_left_derivative_pairing_x H hA hB hp hx hy
  | succ l ih =>
    have h1 := ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)
    have h2 := ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB)
    have h3 := h1.add h2
    rw [← mul_add] at h3
    exact h3

theorem quadrant_function_continuous_on (H : Hyp D Ξ α) {m : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA 0 m A) (hB : AdmW α cB 0 m B) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => QL D q.1 m A B q.2.1 q.2.2) ({p | D.inSS p} ×ˢ Quad) := by
  induction m generalizing A B with
  | zero =>
    have h1 := ph_continuousOn H (admissible_of_weighted hA) (admissible_of_weighted hB)
    have h2 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => dilation₂ q.2 q.1) ({p | D.inSS p} ×ˢ Quad) :=
      (dilationAction_continuousOn k r).mono (Set.prod_mono (Set.subset_univ _) le_rfl)
    refine h1.comp h2 ?_
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact dil_inSS H.dilN D hp ht.1 ht.2
  | succ m ih => exact (ih (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB)).add (ih (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB))

theorem QR_continuousOn (H : Hyp D Ξ α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l m A) (hB : AdmW α cB l m B) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => QR D q.1 m l A B q.2.1 q.2.2) ({p | D.inSS p} ×ˢ Quad) := by
  induction l generalizing A B with
  | zero => exact quadrant_function_continuous_on H hA hB
  | succ l ih => exact (ih (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB)).add (ih (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB))

theorem QR_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (m l : ℕ) (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
    AdmW α cA l m A → AdmW α cB l m B → ∀ p, D.inSS p → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      ∀ y ∈ Set.Icc (1 / 2 : ℝ) 2, ‖QR D p m l A B x y‖ ≤ 2 ^ (m + l) * (K * cA * cB * XX Ξ p) := by
  obtain ⟨K, hK, hb⟩ := phdil_bound H
  refine ⟨K, hK, ?_⟩
  have hQL : ∀ (m : ℕ) (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
      AdmW α cA 0 m A → AdmW α cB 0 m B → ∀ p, D.inSS p → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      ∀ y ∈ Set.Icc (1 / 2 : ℝ) 2, ‖QL D p m A B x y‖ ≤ 2 ^ m * (K * cA * cB * XX Ξ p) := by
    intro m
    induction m with
    | zero =>
      intro A B cA cB hA hB p hp x hx y hy
      simpa [QL] using hb A B cA cB (admissible_of_weighted hA) (admissible_of_weighted hB) p hp x hx y hy
    | succ m ih =>
      intro A B cA cB hA hB p hp x hx y hy
      have h1 := ih (Ll A) B cA cB (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB) p hp x hx y hy
      have h2 := ih A (Ll B) cA cB (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB) p hp x hx y hy
      calc ‖QL D p (m + 1) A B x y‖ ≤ ‖QL D p m (Ll A) B x y‖ + ‖QL D p m A (Ll B) x y‖ := norm_add_le _ _
        _ ≤ 2 ^ m * (K * cA * cB * XX Ξ p) + 2 ^ m * (K * cA * cB * XX Ξ p) := add_le_add h1 h2
        _ = _ := by ring
  intro m l
  induction l with
  | zero =>
    intro A B cA cB hA hB p hp x hx y hy
    exact hQL m A B cA cB hA hB p hp x hx y hy
  | succ l ih =>
    intro A B cA cB hA hB p hp x hx y hy
    have h1 := ih (Rr A) B cA cB (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB) p hp x hx y hy
    have h2 := ih A (Rr B) cA cB (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB) p hp x hx y hy
    calc ‖QR D p m (l + 1) A B x y‖ ≤ ‖QR D p m l (Rr A) B x y‖ + ‖QR D p m l A (Rr B) x y‖ := norm_add_le _ _
      _ ≤ 2 ^ (m + l) * (K * cA * cB * XX Ξ p) + 2 ^ (m + l) * (K * cA * cB * XX Ξ p) := add_le_add h1 h2
      _ = _ := by rw [← add_assoc m l 1]; ring

theorem regBracket_eq (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (x y : ℝ) :
    regBracket D F F' p x y = ((Wd D x * Wd D y : ℝ) : ℂ) * QR D p 0 0 F F' x y := by
  show ((D.χ x * D.χ y * (x * y) ^ kap k r : ℝ) : ℂ) * Ph D F F' (dilation₂ (x, y) p) =
    ((Wd D x * Wd D y : ℝ) : ℂ) * Ph D F F' (dilation₂ (x, y) p)
  congr 2
  unfold Wd
  rw [mul_pow]
  ring

theorem admissibleWeight_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {n m n' m' : ℕ}
    {f : Mat k r → E} (h : AdmW α c n m f) (hn : n' ≤ n) (hm : m' ≤ m) : AdmW α c n' m' f :=
  ⟨fun j hj i hi => h.1 j (hj.trans hn) i (hi.trans hm), fun j hj => h.2.1 j (lt_of_lt_of_le hj hn),
    fun j hj i hi => h.2.2 j (hj.trans hn) i (lt_of_lt_of_le hi hm)⟩

theorem regularised_pairing_continuous_in_t (H : Hyp D Ξ α) {m l : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA l m A) (hB : AdmW α cB l m B) {p : SS k r} (hp : D.inSS p) :
    ContinuousOn (fun t : ℝ × ℝ => QR D p m l A B t.1 t.2) Quad :=
  (QR_continuousOn H hA hB).comp (Continuous.prodMk_right p).continuousOn (fun _ ht => ⟨hp, ht⟩)

theorem regularised_bracket_expansion (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {p : SS k r} (hp : D.inSS p) :
    (∀ x y, oneMinusDD (regBracket D F F' p) x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam (rr r) (Wd D) m x * gam (rr r) (Wd D) l y : ℝ) : ℂ) * QR D p m l F F' x y) ∧
    (∀ x, ContDiff ℝ 2 (fun y => regBracket D F F' p x y)) ∧
    (∀ y, ContDiff ℝ 2 (fun x => regBracket D F F' p x y -
      iteratedDeriv 2 (fun y' => regBracket D F F' p x y') y)) ∧
    (∀ x₁ x₂ : ℝ, (∫ t : ℝ × ℝ, oneMinusDD (regBracket D F F' p) t.1 t.2 *
        Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      (((1 + x₁ ^ 2) * (1 + x₂ ^ 2) : ℝ) : ℂ) *
        ∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 *
          Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) :=
  al2 (Wd_contDiff D) (Wd_tsupport D) (rr r) (fun m l x y => QR D p m l F F' x y)
    (fun l hl x hx y hy => QR_hasDerivAt_y H (admissibleWeight_mono hF (by omega) (by omega))
      (admissibleWeight_mono hF' (by omega) (by omega)) hp hx hy)
    (fun m hm l hl x hx y hy => regularised_pairing_deriv_x H (admissibleWeight_mono hF hl (by omega))
      (admissibleWeight_mono hF' hl (by omega)) hp hx hy)
    (fun m hm l hl => regularised_pairing_continuous_in_t H (admissibleWeight_mono hF hl hm) (admissibleWeight_mono hF' hl hm) hp)
    (regBracket D F F' p) (regBracket_eq D F F' p)

theorem E_formula (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {p : SS k r} (hp : D.inSS p) (t : ℝ × ℝ) :
    oneMinusDD (regBracket D F F' p) t.1 t.2 = Ef D F F' p t := (regularised_bracket_expansion H hF hF' hp).1 t.1 t.2

theorem E_reg (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {p : SS k r} (hp : D.inSS p) :
    (∀ x, ContDiff ℝ 2 (fun y => regBracket D F F' p x y)) ∧
    (∀ y, ContDiff ℝ 2 (fun x => regBracket D F F' p x y -
      iteratedDeriv 2 (fun y' => regBracket D F F' p x y') y)) := ⟨(regularised_bracket_expansion H hF hF' hp).2.1, (regularised_bracket_expansion H hF hF' hp).2.2.1⟩

theorem E_ibp (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {p : SS k r} (hp : D.inSS p) (x₁ x₂ : ℝ) :
    (∫ t : ℝ × ℝ, oneMinusDD (regBracket D F F' p) t.1 t.2 *
        Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      (((1 + x₁ ^ 2) * (1 + x₂ ^ 2) : ℝ) : ℂ) *
        ∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := (regularised_bracket_expansion H hF hF' hp).2.2.2 x₁ x₂

theorem cutoff_gamma_product_zero (D : RealPlaceData k r Wp Wq) (m l : ℕ) {t : ℝ × ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2) :
    gam (rr r) (Wd D) m t.1 * gam (rr r) (Wd D) l t.2 = 0 := by
  by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
  · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h2 => ht ⟨h1, h2⟩
    rw [gam_zero (Wd_tsupport D) _ _ h2, mul_zero]
  · rw [gam_zero (Wd_tsupport D) _ _ h1, zero_mul]

theorem Ef_zero (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) {t : ℝ × ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2) : Ef D F F' p t = 0 := by
  unfold Ef
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun l _ => ?_
  rw [cutoff_gamma_product_zero D m l ht]
  simp

theorem Ef_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
    AdmW α c 2 2 F → AdmW α c' 2 2 F' → ∀ p, D.inSS p → ∀ t, ‖Ef D F F' p t‖ ≤ K * c * c' * XX Ξ p := by
  obtain ⟨K, hK, hb⟩ := QR_bound H
  obtain ⟨Γ, hΓ, hg⟩ := gam_bound (Wd_contDiff D) (Wd_tsupport D) (rr r)
  refine ⟨9 * (Γ * Γ * (16 * K)), by positivity, ?_⟩
  intro F F' c c' hF hF' p hp t
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hX := XX_nonneg Ξ p
  have nn : 0 ≤ K * c * c' * XX Ξ p := by positivity
  by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
  · unfold Ef
    have term : ∀ m ∈ Finset.range 3, ∀ l ∈ Finset.range 3,
        ‖((gam (rr r) (Wd D) m t.1 * gam (rr r) (Wd D) l t.2 : ℝ) : ℂ) * QR D p m l F F' t.1 t.2‖ ≤
          Γ * Γ * (16 * (K * c * c' * XX Ξ p)) := by
      intro m hm l hl
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hm' : m ≤ 2 := by have := Finset.mem_range.1 hm; omega
      have hl' : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
      have q := hb m l F F' c c' (admissibleWeight_mono hF hl' hm') (admissibleWeight_mono hF' hl' hm') p hp t.1
        ⟨ht.1.1.le, ht.1.2.le⟩ t.2 ⟨ht.2.1.le, ht.2.2.le⟩
      have p2 : (2 : ℝ) ^ (m + l) ≤ 16 := by
        calc (2 : ℝ) ^ (m + l) ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 16 := by norm_num
      calc _ ≤ (Γ * Γ) * (2 ^ (m + l) * (K * c * c' * XX Ξ p)) :=
            mul_le_mul (mul_le_mul (hg m _) (hg l _) (abs_nonneg _) hΓ) q (norm_nonneg _) (by positivity)
        _ ≤ _ := by gcongr
    calc _ ≤ ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3, Γ * Γ * (16 * (K * c * c' * XX Ξ p)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => term m hm l hl))
      _ = _ := by simp; ring
  · rw [Ef_zero D F F' p ht, norm_zero]; positivity

theorem box_subset_quadrant {t : ℝ × ℝ} (h : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2) : t ∈ Quad := by
  refine ⟨?_, ?_⟩
  · have := h.1.1
    show (0 : ℝ) < t.1
    linarith
  · have := h.2.1
    show (0 : ℝ) < t.2
    linarith

theorem Et_eq (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p)
    (t : ℝ × ℝ) : Et D F F' (p, t) = Ef D F F' p t := by
  unfold Et
  by_cases ht : t ∈ Quad
  · rw [Set.indicator_of_mem (show (p, t) ∈ {p | D.inSS p} ×ˢ Quad from ⟨hp, ht⟩)]
  · rw [Set.indicator_of_notMem (fun h => ht h.2)]
    exact (Ef_zero D F F' p (fun h => ht (box_subset_quadrant h))).symm

theorem Et_zero (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) {t : ℝ × ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2) : Et D F F' (p, t) = 0 := by
  unfold Et
  by_cases h : (p, t) ∈ {p | D.inSS p} ×ˢ Quad
  · rw [Set.indicator_of_mem h]; exact Ef_zero D F F' p ht
  · exact Set.indicator_of_notMem h _

theorem Et_zero' (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : ¬ D.inSS p)
    (t : ℝ × ℝ) : Et D F F' (p, t) = 0 := Set.indicator_of_notMem (fun h => hp h.1) _

theorem stronglyMeasurable_indicator_of_continuousOn' {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) {f : X → ℂ} (hf : ContinuousOn f s) :
    StronglyMeasurable (s.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact (hf.measurable_piecewise continuousOn_const hs).stronglyMeasurable

theorem cutoff_gamma_product_continuous (D : RealPlaceData k r Wp Wq) (m l : ℕ) :
    Continuous (fun t : ℝ × ℝ => ((gam (rr r) (Wd D) m t.1 * gam (rr r) (Wd D) l t.2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp
    (((gam_continuous (Wd_contDiff D) (Wd_tsupport D) (rr r) m).comp continuous_fst).mul
      ((gam_continuous (Wd_contDiff D) (Wd_tsupport D) (rr r) l).comp continuous_snd))

theorem continuousOn_averaged_pairing_quadrant (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => Ef D F F' q.1 q.2) ({p | D.inSS p} ×ˢ Quad) := by
  unfold Ef
  refine continuousOn_finsetSum _ fun m hm => continuousOn_finsetSum _ fun l hl => ?_
  have hm' : m ≤ 2 := by have := Finset.mem_range.1 hm; omega
  have hl' : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
  exact ((cutoff_gamma_product_continuous D m l).comp continuous_snd).continuousOn.mul
    (QR_continuousOn H (admissibleWeight_mono hF hl' hm') (admissibleWeight_mono hF' hl' hm'))

theorem quadrant_is_open : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioi

theorem continuous_mul_of_vanishing_outside_box {u v : ℝ × ℝ → ℂ} (hu : Continuous u)
    (hz : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2 → u t = 0) (hv : ContinuousOn v Quad) :
    Continuous (fun t => u t * v t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t ∈ Quad
  · exact hu.continuousAt.mul (hv.continuousAt (quadrant_is_open.mem_nhds ht))
  · have hB : IsClosed (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) := isClosed_Icc.prod isClosed_Icc
    have htB : t ∈ (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2)ᶜ := by
      intro h
      apply ht
      refine ⟨?_, ?_⟩
      · have := h.1.1
        show (0 : ℝ) < t.1
        linarith
      · have := h.2.1
        show (0 : ℝ) < t.2
        linarith
    have : (fun t => u t * v t) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [hB.isOpen_compl.mem_nhds htB] with s hs
      rw [hz s (fun h => hs ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩), zero_mul]
    exact continuousAt_const.congr this.symm

theorem Et_measurable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') : StronglyMeasurable (Et D F F') := stronglyMeasurable_indicator_of_continuousOn' ((measurableSet_inSS D).prod (measurableSet_Ioi.prod measurableSet_Ioi))
    (continuousOn_averaged_pairing_quadrant H hF hF')

theorem Et_continuous (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (p : SS k r) : Continuous (fun t : ℝ × ℝ => Et D F F' (p, t)) := by
  by_cases hp : D.inSS p
  · have e : (fun t : ℝ × ℝ => Et D F F' (p, t)) = fun t => Ef D F F' p t := funext (Et_eq D F F' hp)
    rw [e]
    unfold Ef
    refine continuous_finsetSum _ fun m hm => continuous_finsetSum _ fun l hl => ?_
    have hm' : m ≤ 2 := by have := Finset.mem_range.1 hm; omega
    have hl' : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
    refine continuous_mul_of_vanishing_outside_box (cutoff_gamma_product_continuous D m l) (fun t ht => ?_)
      (regularised_pairing_continuous_in_t H (admissibleWeight_mono hF hl' hm') (admissibleWeight_mono hF' hl' hm') hp)
    rw [cutoff_gamma_product_zero D m l ht]; simp
  · have e : (fun t : ℝ × ℝ => Et D F F' (p, t)) = fun _ => 0 := funext (Et_zero' D F F' hp)
    rw [e]
    exact continuous_const

theorem cutoff_weight_zero_outside (D : RealPlaceData k r Wp Wq) {t : ℝ} (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2) : Wd D t = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => ht (Wd_tsupport D h))

theorem cutoff_square_product_zero (D : RealPlaceData k r Wp Wq) {t : ℝ × ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2) : Wd D t.1 * Wd D t.2 = 0 := by
  by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
  · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h2 => ht ⟨h1, h2⟩
    rw [cutoff_weight_zero_outside D h2, mul_zero]
  · rw [cutoff_weight_zero_outside D h1, zero_mul]

theorem regularized_bracket_zero_off_box (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) {t : ℝ × ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2) : regBracket D F F' p t.1 t.2 = 0 := by
  rw [regBracket_eq, cutoff_square_product_zero D ht]
  simp

theorem cutoff_square_product_continuous (D : RealPlaceData k r Wp Wq) :
    Continuous (fun t : ℝ × ℝ => ((Wd D t.1 * Wd D t.2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp
    (((Wd_contDiff D).continuous.comp continuous_fst).mul ((Wd_contDiff D).continuous.comp continuous_snd))

theorem Bt_eq (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p)
    (t : ℝ × ℝ) : Bt D F F' (p, t) = regBracket D F F' p t.1 t.2 := by
  unfold Bt
  by_cases ht : t ∈ Quad
  · rw [Set.indicator_of_mem (show (p, t) ∈ {p | D.inSS p} ×ˢ Quad from ⟨hp, ht⟩)]
  · rw [Set.indicator_of_notMem (fun h => ht h.2)]
    exact (regularized_bracket_zero_off_box D F F' p (fun h => ht (box_subset_quadrant h))).symm

theorem Bt_zero (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) {t : ℝ × ℝ}
    (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2) : Bt D F F' (p, t) = 0 := by
  unfold Bt
  by_cases h : (p, t) ∈ {p | D.inSS p} ×ˢ Quad
  · rw [Set.indicator_of_mem h]; exact regularized_bracket_zero_off_box D F F' p ht
  · exact Set.indicator_of_notMem h _

theorem Bt_zero' (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : ¬ D.inSS p)
    (t : ℝ × ℝ) : Bt D F F' (p, t) = 0 := Set.indicator_of_notMem (fun h => hp h.1) _

theorem Bt_measurable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') : StronglyMeasurable (Bt D F F') := by
  refine stronglyMeasurable_indicator_of_continuousOn' ((measurableSet_inSS D).prod (measurableSet_Ioi.prod measurableSet_Ioi)) ?_
  have e : (fun q : SS k r × (ℝ × ℝ) => regBracket D F F' q.1 q.2.1 q.2.2) =
      fun q => ((Wd D q.2.1 * Wd D q.2.2 : ℝ) : ℂ) * QR D q.1 0 0 F F' q.2.1 q.2.2 :=
    funext fun q => regBracket_eq D F F' q.1 q.2.1 q.2.2
  rw [e]
  exact ((cutoff_square_product_continuous D).comp continuous_snd).continuousOn.mul
    (QR_continuousOn H (admissibleWeight_mono hF (by omega) (by omega)) (admissibleWeight_mono hF' (by omega) (by omega)))

theorem Bt_continuous (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (p : SS k r) : Continuous (fun t : ℝ × ℝ => Bt D F F' (p, t)) := by
  by_cases hp : D.inSS p
  · have e : (fun t : ℝ × ℝ => Bt D F F' (p, t)) =
        fun t => ((Wd D t.1 * Wd D t.2 : ℝ) : ℂ) * QR D p 0 0 F F' t.1 t.2 :=
      funext fun t => (Bt_eq D F F' hp t).trans (regBracket_eq D F F' p t.1 t.2)
    rw [e]
    refine continuous_mul_of_vanishing_outside_box (cutoff_square_product_continuous D) (fun t ht => ?_)
      (regularised_pairing_continuous_in_t H (admissibleWeight_mono hF (by omega) (by omega)) (admissibleWeight_mono hF' (by omega) (by omega)) hp)
    rw [cutoff_square_product_zero D ht]; simp
  · have e : (fun t : ℝ × ℝ => Bt D F F' (p, t)) = fun _ => 0 := funext (Bt_zero' D F F' hp)
    rw [e]
    exact continuous_const

theorem Bt_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
    AdmW α c 2 2 F → AdmW α c' 2 2 F' → ∀ p t, ‖Bt D F F' (p, t)‖ ≤ K * c * c' * XX Ξ p := by
  obtain ⟨K, hK, hb⟩ := QR_bound H
  have hcs : HasCompactSupport (Wd D) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      ((Wd_tsupport D).trans Set.Ioo_subset_Icc_self)
  obtain ⟨C, hC⟩ := (Wd_contDiff D).continuous.bounded_above_of_compact_support hcs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C * C * K, by positivity, ?_⟩
  intro F F' c c' hF hF' p t
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hX := XX_nonneg Ξ p
  have nn : 0 ≤ K * c * c' * XX Ξ p := by positivity
  by_cases hp : D.inSS p
  · by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
    · rw [Bt_eq D F F' hp, regBracket_eq, norm_mul, Complex.norm_real, norm_mul]
      have q := hb 0 0 F F' c c' (admissibleWeight_mono hF (by omega) (by omega))
        (admissibleWeight_mono hF' (by omega) (by omega)) p hp t.1
        ⟨ht.1.1.le, ht.1.2.le⟩ t.2 ⟨ht.2.1.le, ht.2.2.le⟩
      simp only [add_zero, pow_zero, one_mul] at q
      calc _ ≤ (C * C) * (K * c * c' * XX Ξ p) :=
            mul_le_mul (mul_le_mul (hC _) (hC _) (norm_nonneg _) hC0) q (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [Bt_zero D F F' p ht, norm_zero]; positivity
  · rw [Bt_zero' D F F' hp, norm_zero]; positivity

theorem Et_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
    AdmW α c 2 2 F → AdmW α c' 2 2 F' → ∀ p t, ‖Et D F F' (p, t)‖ ≤ K * c * c' * XX Ξ p := by
  obtain ⟨K, hK, hb⟩ := Ef_bound H
  refine ⟨K, hK, ?_⟩
  intro F F' c c' hF hF' p t
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hX := XX_nonneg Ξ p
  by_cases hp : D.inSS p
  · rw [Et_eq D F F' hp]; exact hb F F' c c' hF hF' p hp t
  · rw [Et_zero' D F F' hp, norm_zero]; positivity

theorem betaInfTau_eq (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) : betaInfTau D τ F F' = ∫ p, Gt D F F' τ p ∂D.μSS := by
  unfold betaInfTau
  refine integral_congr_ae ?_
  filter_upwards [ae_inSS D] with p hp
  unfold Gt wt phase
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only []
  rw [E_formula H hF hF' hp t, Et_eq D F F' hp t]

theorem Gt_measurable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') : StronglyMeasurable (fun x : (ℝ × ℝ) × SS k r => Gt D F F' x.1 x.2) := by
  have o1 : OpensMeasurableSpace ((ℝ × ℝ) × SS k r) := Prod.opensMeasurableSpace
  have o2 : OpensMeasurableSpace (((ℝ × ℝ) × SS k r) × (ℝ × ℝ)) := Prod.opensMeasurableSpace
  have h1 : StronglyMeasurable (fun x : (ℝ × ℝ) × SS k r => ((wt D x.1 x.2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (wt_continuous D)).stronglyMeasurable
  have h2 : StronglyMeasurable (fun y : ((ℝ × ℝ) × SS k r) × (ℝ × ℝ) =>
      Et D F F' (y.1.2, y.2) * Complex.exp (Complex.I * (phase D y.1.1 y.1.2 y.2 : ℂ))) := by
    refine StronglyMeasurable.mul ((Et_measurable H hF hF').comp_measurable (by fun_prop))
      (Continuous.stronglyMeasurable ?_)
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (phase_continuous D)))
  exact h1.mul h2.integral_prod_right'

theorem Gt_bound (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
    AdmW α c 2 2 F → AdmW α c' 2 2 F' → ∀ τ p, ‖Gt D F F' τ p‖ ≤ wt D τ p * (K * c * c' * XX Ξ p) := by
  obtain ⟨K, hK, hb⟩ := Et_bound H
  have hBc : IsCompact (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) := isCompact_Icc.prod isCompact_Icc
  have hBm : MeasurableSet (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) := hBc.isClosed.measurableSet
  refine ⟨K * (volume.real (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2)), by positivity, ?_⟩
  intro F F' c c' hF hF' τ p
  unfold Gt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg D τ p)]
  refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg D τ p)
  have key : ∀ t : ℝ × ℝ, ‖Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))‖ ≤
      (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2).indicator (fun _ => K * c * c' * XX Ξ p) t := by
    intro t
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    by_cases ht : t ∈ Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2
    · rw [Set.indicator_of_mem ht]; exact hb F F' c c' hF hF' p t
    · rw [Set.indicator_of_notMem ht, Et_zero D F F' p
        (fun h => ht ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩), norm_zero]
  have hint : Integrable ((Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2).indicator
      (fun _ : ℝ × ℝ => K * c * c' * XX Ξ p)) volume :=
    (integrable_indicator_iff hBm).2 (continuousOn_const.integrableOn_compact hBc)
  calc _ ≤ ∫ t, (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2).indicator
        (fun _ : ℝ × ℝ => K * c * c' * XX Ξ p) t := norm_integral_le_of_norm_le hint (ae_of_all _ key)
    _ = _ := by
      rw [integral_indicator hBm, setIntegral_const, smul_eq_mul]
      ring

theorem Gt_eq (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) (p : SS k r) :
    Gt D F F' τ p = ∫ t : ℝ × ℝ, Bt D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ)) := by
  by_cases hp : D.inSS p
  · unfold Gt
    have e1 : (∫ t : ℝ × ℝ, Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))) =
        ∫ t : ℝ × ℝ, oneMinusDD (regBracket D F F' p) t.1 t.2 * Complex.exp (Complex.I *
          ((τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 : ℝ) : ℂ)) := by
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only []
      rw [Et_eq D F F' hp, E_formula H hF hF' hp]
      have : phase D τ p t =
          τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 := by
        unfold phase; ring
      rw [this]
    have e2 : (∫ t : ℝ × ℝ, Bt D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))) =
        ∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 * Complex.exp (Complex.I *
          ((τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 : ℝ) : ℂ)) := by
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only []
      rw [Bt_eq D F F' hp]
      have : phase D τ p t =
          τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 := by
        unfold phase; ring
      rw [this]
    rw [e1, e2, E_ibp H hF hF' hp, ← mul_assoc, ← Complex.ofReal_mul]
    have : wt D τ p * ((1 + (τ.1 * lam k r D.z (Matrix.of p.1.2)) ^ 2) *
        (1 + (-(τ.2 * lam k r D.z' (Matrix.of p.2.2))) ^ 2)) = 1 := by
      unfold wt
      have a1 : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2) ≠ 0 := by positivity
      have a2 : (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2) ≠ 0 := by positivity
      field_simp
    rw [this]
    simp
  · simp [Gt, Et_zero' D F F' hp, Bt_zero' D F F' hp]

end shared

section regbound

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem weight_dominated_near_quadrant (D : RealPlaceData k r Wp Wq) {τ₀ : ℝ × ℝ} (h₀ : τ₀ ∈ Quad) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ × ℝ, τ₀.1 / 2 < τ.1 → τ₀.2 / 2 < τ.2 → ∀ p, wt D τ p ≤ M * LL D p := by
  have a1 : 0 < τ₀.1 := h₀.1
  have a2 : 0 < τ₀.2 := h₀.2
  refine ⟨4 * max 1 ((τ₀.1 / 2) ^ 2)⁻¹ * max 1 ((τ₀.2 / 2) ^ 2)⁻¹, by positivity, ?_⟩
  intro τ h1 h2 p
  have b1 : 0 < τ.1 := lt_trans (by positivity) h1
  have b2 : 0 < τ.2 := lt_trans (by positivity) h2
  refine (wt_le D b1 b2 p).trans ?_
  have c1 : max 1 (τ.1 ^ 2)⁻¹ ≤ max 1 ((τ₀.1 / 2) ^ 2)⁻¹ := by
    apply max_le_max le_rfl
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) h1.le 2
  have c2 : max 1 (τ.2 ^ 2)⁻¹ ≤ max 1 ((τ₀.2 / 2) ^ 2)⁻¹ := by
    apply max_le_max le_rfl
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) h2.le 2
  have hL := LL_nonneg D p
  gcongr

theorem half_quadrant_neighbourhood {τ₀ : ℝ × ℝ} (h₀ : τ₀ ∈ Quad) :
    {τ : ℝ × ℝ | τ₀.1 / 2 < τ.1 ∧ τ₀.2 / 2 < τ.2} ∈ 𝓝 τ₀ := by
  have a1 : 0 < τ₀.1 := h₀.1
  have a2 : 0 < τ₀.2 := h₀.2
  have ho : IsOpen {τ : ℝ × ℝ | τ₀.1 / 2 < τ.1 ∧ τ₀.2 / 2 < τ.2} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
  exact ho.mem_nhds ⟨by linarith, by linarith⟩

theorem aestronglyMeasurable_beta_integrand (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) : AEStronglyMeasurable (Gt D F F' τ) D.μSS :=
  ((Gt_measurable H hF hF').comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem pairing_kernel_integrable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {τ : ℝ × ℝ} (hτ : τ ∈ Quad) : Integrable (Gt D F F' τ) D.μSS := by
  obtain ⟨K, hK, hb⟩ := Gt_bound H
  obtain ⟨M, hM, hw⟩ := weight_dominated_near_quadrant D hτ
  have a1 : 0 < τ.1 := hτ.1
  have a2 : 0 < τ.2 := hτ.2
  refine Integrable.mono' ((xi_integrable H).const_mul (M * (K * c * c'))) (aestronglyMeasurable_beta_integrand H hF hF' τ) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hX := XX_nonneg Ξ p
  calc ‖Gt D F F' τ p‖ ≤ wt D τ p * (K * c * c' * XX Ξ p) := hb F F' c c' hF hF' τ p
    _ ≤ (M * LL D p) * (K * c * c' * XX Ξ p) := by
        apply mul_le_mul_of_nonneg_right (hw τ (by linarith) (by linarith) p)
        positivity
    _ = M * (K * c * c') * (XX Ξ p * LL D p) := by ring

theorem locally_bounded_betaInfTau (H : Hyp D Ξ α) {τ₀ : ℝ × ℝ} (h₀ : τ₀ ∈ Quad) :
    ∃ C : ℝ, ∃ U ∈ 𝓝 τ₀, ∀ τ ∈ U, ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
      CCle α 4 F c → CCle α 4 F' c' → ‖betaInfTau D τ F F'‖ ≤ C * c * c' := by
  obtain ⟨K, hK, hb⟩ := Gt_bound H
  obtain ⟨M, hM, hw⟩ := weight_dominated_near_quadrant D h₀
  refine ⟨M * K * ∫ p, XX Ξ p * LL D p ∂D.μSS, _, half_quadrant_neighbourhood h₀, ?_⟩
  intro τ hτ F F' c c' hcF hcF'
  have hF := admissible_weighted_of_bound hcF
  have hF' := admissible_weighted_of_bound hcF'
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  rw [betaInfTau_eq H hF hF' τ]
  have key : ‖∫ p, Gt D F F' τ p ∂D.μSS‖ ≤ ∫ p, M * (K * c * c') * (XX Ξ p * LL D p) ∂D.μSS := by
    apply norm_integral_le_of_norm_le ((xi_integrable H).const_mul (M * (K * c * c')))
    refine Filter.Eventually.of_forall fun p => ?_
    have hX := XX_nonneg Ξ p
    calc ‖Gt D F F' τ p‖ ≤ wt D τ p * (K * c * c' * XX Ξ p) := hb F F' c c' hF hF' τ p
      _ ≤ (M * LL D p) * (K * c * c' * XX Ξ p) := by
          apply mul_le_mul_of_nonneg_right (hw τ hτ.1 hτ.2 p)
          positivity
      _ = M * (K * c * c') * (XX Ξ p * LL D p) := by ring
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

theorem error_term_integrable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (p : SS k r) : Integrable (fun t : ℝ × ℝ => Et D F F' (p, t)) := by
  apply (Et_continuous H hF hF' p).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2)
    (isCompact_Icc.prod isCompact_Icc)
  intro t ht
  apply Et_zero
  intro h
  exact ht ⟨Set.Ioo_subset_Icc_self h.1, Set.Ioo_subset_Icc_self h.2⟩

theorem norm_exp_I_mul_real_eq_one (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

theorem integrable_pairing_times_phase_exp (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) (p : SS k r) :
    Integrable (fun t : ℝ × ℝ => Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))) := by
  have hph : Continuous (fun t : ℝ × ℝ => phase D τ p t) :=
    (phase_continuous D).comp (f := fun t : ℝ × ℝ => ((τ, p), t)) (continuous_const.prodMk continuous_id)
  have hE := Et_continuous H hF hF' p
  have hcont : Continuous (fun t : ℝ × ℝ => Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))) := by
    fun_prop
  refine (error_term_integrable H hF hF' p).norm.mono' hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_mul, norm_exp_I_mul_real_eq_one, mul_one]

theorem continuous_beta_integrand_in_tau (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (p : SS k r) : Continuous (fun τ : ℝ × ℝ => Gt D F F' τ p) := by
  unfold Gt
  have hw : Continuous (fun τ : ℝ × ℝ => wt D τ p) :=
    (wt_continuous D).comp (f := fun τ : ℝ × ℝ => (τ, p)) (continuous_id.prodMk continuous_const)
  refine (Complex.continuous_ofReal.comp hw).mul ?_
  apply continuous_of_dominated (bound := fun t : ℝ × ℝ => ‖Et D F F' (p, t)‖)
  · intro τ
    exact (integrable_pairing_times_phase_exp H hF hF' τ p).aestronglyMeasurable
  · intro τ
    refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, norm_exp_I_mul_real_eq_one, mul_one]
  · exact (error_term_integrable H hF hF' p).norm
  · refine Filter.Eventually.of_forall fun t => ?_
    have hph : Continuous (fun τ : ℝ × ℝ => phase D τ p t) :=
      (phase_continuous D).comp (f := fun τ : ℝ × ℝ => ((τ, p), t))
        ((continuous_id.prodMk continuous_const).prodMk continuous_const)
    fun_prop

theorem regularised_pairing_continuous (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hcF : InCC α 4 F) (hcF' : InCC α 4 F') :
    ContinuousOn (fun τ => betaInfTau D τ F F') Quad := by
  obtain ⟨c, hc⟩ := hcF
  obtain ⟨c', hc'⟩ := hcF'
  have hF := admissible_weighted_of_bound hc
  have hF' := admissible_weighted_of_bound hc'
  have e : (fun τ => betaInfTau D τ F F') = fun τ => ∫ p, Gt D F F' τ p ∂D.μSS := by
    funext τ; exact betaInfTau_eq H hF hF' τ
  rw [e]
  intro τ₀ h₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨K, hK, hb⟩ := Gt_bound H
  obtain ⟨M, hM, hw⟩ := weight_dominated_near_quadrant D h₀
  have hcn := admissible_constant_nonneg (admissible_of_weighted hF)
  have hcn' := admissible_constant_nonneg (admissible_of_weighted hF')
  apply continuousAt_of_dominated (bound := fun p => M * (K * c * c') * (XX Ξ p * LL D p))
  · exact Filter.Eventually.of_forall fun τ => aestronglyMeasurable_beta_integrand H hF hF' τ
  · filter_upwards [half_quadrant_neighbourhood h₀] with τ hτ
    refine Filter.Eventually.of_forall fun p => ?_
    have hX := XX_nonneg Ξ p
    calc ‖Gt D F F' τ p‖ ≤ wt D τ p * (K * c * c' * XX Ξ p) := hb F F' c c' hF hF' τ p
      _ ≤ (M * LL D p) * (K * c * c' * XX Ξ p) := by
          apply mul_le_mul_of_nonneg_right (hw τ hτ.1 hτ.2 p)
          positivity
      _ = M * (K * c * c') * (XX Ξ p * LL D p) := by ring
  · exact (xi_integrable H).const_mul _
  · exact Filter.Eventually.of_forall fun p => (continuous_beta_integrand_in_tau H hF hF' p).continuousAt

theorem phase_function_add_left (H : Hyp D Ξ α) {A₁ A₂ B : Mat k r → (Wq →L[ℂ] Wp)} {c₁ c₂ cB : ℝ} (h₁ : admitted α c₁ A₁)
    (h₂ : admitted α c₂ A₂) (hB : admitted α cB B) {q : SS k r} (hq : D.inSS q) :
    Ph D (A₁ + A₂) B q = Ph D A₁ B q + Ph D A₂ B q := by
  unfold Ph
  rw [← integral_add (ph_integrable H h₁ hB hq) (ph_integrable H h₂ hB hq)]
  congr 1
  funext g
  rw [rho_eq, rho_eq, rho_eq, Pi.add_apply, map_add, hsInner_add_left]

theorem phase_function_add_right (H : Hyp D Ξ α) {A B₁ B₂ : Mat k r → (Wq →L[ℂ] Wp)} {cA c₁ c₂ : ℝ} (hA : admitted α cA A)
    (h₁ : admitted α c₁ B₁) (h₂ : admitted α c₂ B₂) {q : SS k r} (hq : D.inSS q) :
    Ph D A (B₁ + B₂) q = Ph D A B₁ q + Ph D A B₂ q := by
  unfold Ph
  rw [← integral_add (ph_integrable H hA h₁ hq) (ph_integrable H hA h₂ hq)]
  congr 1
  funext g
  rw [Pi.add_apply, hsInner_add_right]

theorem pairing_smul_left_bis (D : RealPlaceData k r Wp Wq) (a : ℂ) (A B : Mat k r → (Wq →L[ℂ] Wp)) (q : SS k r) :
    Ph D (a • A) B q = a * Ph D A B q := by
  unfold Ph
  rw [← integral_const_mul]
  congr 1
  funext g
  rw [rho_eq, rho_eq, Pi.smul_apply, map_smul, hsInner_smul_left]

theorem phase_function_smul_right (D : RealPlaceData k r Wp Wq) (a : ℂ) (A B : Mat k r → (Wq →L[ℂ] Wp)) (q : SS k r) :
    Ph D A (a • B) q = conj a * Ph D A B q := by
  unfold Ph
  rw [← integral_const_mul]
  congr 1
  funext g
  rw [Pi.smul_apply, hsInner_smul_right]

theorem cutoff_support_positive (D : RealPlaceData k r Wp Wq) {t : ℝ} (h : D.χ t ≠ 0) : 0 < t := by
  have h1 := (D.χ_supp (subset_tsupport _ (Function.mem_support.2 h))).1
  linarith

theorem regularized_bracket_additive (H : Hyp D Ξ α) {X Y X₁ Y₁ X₂ Y₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ q, D.inSS q → Ph D X Y q = Ph D X₁ Y₁ q + Ph D X₂ Y₂ q) {p : SS k r} (hp : D.inSS p) :
    regBracket D X Y p = fun x y => regBracket D X₁ Y₁ p x y + regBracket D X₂ Y₂ p x y := by
  funext x y
  unfold regBracket
  by_cases h1 : D.χ x = 0
  · simp [h1]
  by_cases h2 : D.χ y = 0
  · simp [h2]
  rw [h _ (dil_inSS H.dilN D hp (cutoff_support_positive D h1) (cutoff_support_positive D h2))]
  ring

theorem betaInfTau_additive_of_pairing_additive (H : Hyp D Ξ α) {X Y X₁ Y₁ X₂ Y₂ : Mat k r → (Wq →L[ℂ] Wp)} {c₁ c₁' c₂ c₂' : ℝ}
    (hX₁ : AdmW α c₁ 2 2 X₁) (hY₁ : AdmW α c₁' 2 2 Y₁) (hX₂ : AdmW α c₂ 2 2 X₂) (hY₂ : AdmW α c₂' 2 2 Y₂)
    (h : ∀ q, D.inSS q → Ph D X Y q = Ph D X₁ Y₁ q + Ph D X₂ Y₂ q) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) :
    betaInfTau D τ X Y = betaInfTau D τ X₁ Y₁ + betaInfTau D τ X₂ Y₂ := by
  rw [betaInfTau_eq H hX₁ hY₁ τ, betaInfTau_eq H hX₂ hY₂ τ,
    ← integral_add (pairing_kernel_integrable H hX₁ hY₁ hτ) (pairing_kernel_integrable H hX₂ hY₂ hτ)]
  unfold betaInfTau
  apply integral_congr_ae
  filter_upwards [ae_inSS D] with p hp
  have e : ∀ t : ℝ × ℝ, oneMinusDD (regBracket D X Y p) t.1 t.2 = Et D X₁ Y₁ (p, t) + Et D X₂ Y₂ (p, t) := by
    intro t
    rw [regularized_bracket_additive H h hp, oneMinusDD_add (E_reg H hX₁ hY₁ hp).1 (E_reg H hX₂ hY₂ hp).1
      (E_reg H hX₁ hY₁ hp).2 (E_reg H hX₂ hY₂ hp).2, E_formula H hX₁ hY₁ hp t, E_formula H hX₂ hY₂ hp t,
      Et_eq D X₁ Y₁ hp t, Et_eq D X₂ Y₂ hp t]
  simp only [e]
  unfold Gt
  rw [← mul_add, ← integral_add (integrable_pairing_times_phase_exp H hX₁ hY₁ τ p) (integrable_pairing_times_phase_exp H hX₂ hY₂ τ p)]
  simp only [add_mul]
  rfl

theorem regularised_pairing_smul (D : RealPlaceData k r Wp Wq) {X Y X₁ Y₁ : Mat k r → (Wq →L[ℂ] Wp)} (a : ℂ)
    (h : ∀ q, Ph D X Y q = a * Ph D X₁ Y₁ q) (τ : ℝ × ℝ) :
    betaInfTau D τ X Y = a * betaInfTau D τ X₁ Y₁ := by
  have e : ∀ p, regBracket D X Y p = fun x y => a * regBracket D X₁ Y₁ p x y := by
    intro p
    funext x y
    unfold regBracket
    rw [h]
    ring
  unfold betaInfTau
  rw [← integral_const_mul]
  congr 1
  funext p
  rw [e p]
  simp only [oneMinusDD_const_mul, mul_assoc]
  rw [integral_const_mul]
  ring

theorem regularised_pairing_sesquilinear (H : Hyp D Ξ α) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) : SesqOn (InCC α 4) (betaInfTau D τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x x' y ⟨c, hc⟩ ⟨c', hc'⟩ ⟨d, hd⟩
    have hx := admissible_weighted_of_bound hc
    have hx' := admissible_weighted_of_bound hc'
    have hy := admissible_weighted_of_bound hd
    exact betaInfTau_additive_of_pairing_additive H hx hy hx' hy
      (fun q hq => phase_function_add_left H (admissible_of_weighted hx) (admissible_of_weighted hx') (admissible_of_weighted hy) hq) hτ
  · rintro x y y' ⟨c, hc⟩ ⟨d, hd⟩ ⟨d', hd'⟩
    have hx := admissible_weighted_of_bound hc
    have hy := admissible_weighted_of_bound hd
    have hy' := admissible_weighted_of_bound hd'
    exact betaInfTau_additive_of_pairing_additive H hx hy hx hy'
      (fun q hq => phase_function_add_right H (admissible_of_weighted hx) (admissible_of_weighted hy) (admissible_of_weighted hy') hq) hτ
  · intro a x y _ _
    exact regularised_pairing_smul D a (fun q => pairing_smul_left_bis D a x y q) τ
  · intro a x y _ _
    exact regularised_pairing_smul D (conj a) (fun q => phase_function_smul_right D a x y q) τ

theorem regBound_of_hyp (H : Hyp D Ξ α) : RegBound D α :=
  ⟨fun _ h₀ => locally_bounded_betaInfTau H h₀, fun _ _ hF hF' => regularised_pairing_continuous H hF hF', fun _ hτ => regularised_pairing_sesquilinear H hτ⟩

end regbound

section avg1

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem exists_bound_isTest_support {w : ℝ → ℝ} (h : IsTest w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, w τ ≠ 0 → 0 < τ ∧ max 1 (τ ^ 2)⁻¹ ≤ M := by
  obtain ⟨_, hc, hs⟩ := h
  have hcont : ContinuousOn (fun τ : ℝ => (τ ^ 2)⁻¹) (tsupport w) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro τ hτ
    have : 0 < τ := hs hτ
    positivity
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn hcont
  refine ⟨max 1 M, le_trans zero_le_one (le_max_left _ _), fun τ hτ => ?_⟩
  have hmem : τ ∈ tsupport w := subset_tsupport _ hτ
  refine ⟨hs hmem, ?_⟩
  have := hM τ hmem
  rw [Real.norm_eq_abs] at this
  exact max_le_max le_rfl ((le_abs_self _).trans this)

theorem integrable_of_isTest' {w : ℝ → ℝ} (h : IsTest w) : Integrable w :=
  h.1.continuous.integrable_of_hasCompactSupport h.2.1

theorem product_test_integrable {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun τ : ℝ × ℝ => |w₁ τ.1| * |w₂ τ.2|) := by
  rw [Measure.volume_eq_prod]
  exact Integrable.mul_prod (integrable_of_isTest' h₁).abs (integrable_of_isTest' h₂).abs

theorem joint_weighted_integrable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun x : (ℝ × ℝ) × SS k r => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) * Gt D F F' x.1 x.2)
      ((volume : Measure (ℝ × ℝ)).prod D.μSS) := by
  have := sigmaFinite_μSS D
  obtain ⟨K, hK0, hK⟩ := Gt_bound H
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound_isTest_support h₁
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_isTest_support h₂
  have hc : 0 ≤ c := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' : 0 ≤ c' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hb : Integrable (fun x : (ℝ × ℝ) × SS k r => (|w₁ x.1.1| * |w₂ x.1.2|) *
      ((4 * M₁ * M₂ * (K * c * c')) * (XX Ξ x.2 * LL D x.2))) ((volume : Measure (ℝ × ℝ)).prod D.μSS) :=
    Integrable.mul_prod (f := fun τ : ℝ × ℝ => |w₁ τ.1| * |w₂ τ.2|)
      (g := fun p : SS k r => (4 * M₁ * M₂ * (K * c * c')) * (XX Ξ p * LL D p))
      (product_test_integrable h₁ h₂) ((xi_integrable H).const_mul _)
  have hmeas : AEStronglyMeasurable
      (fun x : (ℝ × ℝ) × SS k r => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) * Gt D F F' x.1 x.2)
      ((volume : Measure (ℝ × ℝ)).prod D.μSS) := by
    apply AEStronglyMeasurable.mul _ (Gt_measurable H hF hF').aestronglyMeasurable
    have h1c := h₁.1.continuous
    have h2c := h₂.1.continuous
    exact ((by fun_prop : Continuous fun τ : ℝ × ℝ =>
      ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)).stronglyMeasurable.comp_measurable measurable_fst).aestronglyMeasurable
  refine hb.mono' hmeas (ae_of_all _ fun x => ?_)
  have hXX := XX_nonneg Ξ x.2
  have hLL := LL_nonneg D x.2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  by_cases ha : w₁ x.1.1 = 0
  · rw [ha]; simp
  by_cases hb' : w₂ x.1.2 = 0
  · rw [hb']; simp
  obtain ⟨p1, q1⟩ := hM₁ _ ha
  obtain ⟨p2, q2⟩ := hM₂ _ hb'
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hB : 0 ≤ K * c * c' * XX Ξ x.2 := by positivity
  calc ‖Gt D F F' x.1 x.2‖ ≤ wt D x.1 x.2 * (K * c * c' * XX Ξ x.2) := hK F F' c c' hF hF' x.1 x.2
    _ ≤ (4 * max 1 (x.1.1 ^ 2)⁻¹ * max 1 (x.1.2 ^ 2)⁻¹ * LL D x.2) * (K * c * c' * XX Ξ x.2) :=
        mul_le_mul_of_nonneg_right (wt_le D p1 p2 x.2) hB
    _ ≤ (4 * M₁ * M₂ * LL D x.2) * (K * c * c' * XX Ξ x.2) := by
        apply mul_le_mul_of_nonneg_right _ hB
        apply mul_le_mul_of_nonneg_right _ hLL
        have : (0:ℝ) ≤ max 1 (x.1.2 ^ 2)⁻¹ := le_trans zero_le_one (le_max_left _ _)
        calc 4 * max 1 (x.1.1 ^ 2)⁻¹ * max 1 (x.1.2 ^ 2)⁻¹ ≤ 4 * M₁ * max 1 (x.1.2 ^ 2)⁻¹ := by
              apply mul_le_mul_of_nonneg_right _ this
              linarith
          _ ≤ 4 * M₁ * M₂ := by
              apply mul_le_mul_of_nonneg_left q2 (by positivity)
    _ = 4 * M₁ * M₂ * (K * c * c') * (XX Ξ x.2 * LL D x.2) := by ring

theorem regularised_kernel_integrable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (p : SS k r) : Integrable (fun t : ℝ × ℝ => Bt D F F' (p, t)) := by
  apply (Bt_continuous H hF hF' p).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2)
    (isCompact_Icc.prod isCompact_Icc)
  intro t ht
  apply Bt_zero
  intro h
  exact ht ⟨Set.Ioo_subset_Icc_self h.1, Set.Ioo_subset_Icc_self h.2⟩

theorem integrable_test_weighted_phase_product (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (p : SS k r) :
    Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) *
      (Bt D F F' (p, x.2) * Complex.exp (Complex.I * (phase D x.1 p x.2 : ℂ))))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
  have hb : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => (|w₁ x.1.1| * |w₂ x.1.2|) * ‖Bt D F F' (p, x.2)‖)
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) :=
    Integrable.mul_prod (f := fun τ : ℝ × ℝ => |w₁ τ.1| * |w₂ τ.2|)
      (g := fun t : ℝ × ℝ => ‖Bt D F F' (p, t)‖)
      (product_test_integrable h₁ h₂) (regularised_kernel_integrable H hF hF' p).norm
  have h1c := h₁.1.continuous
  have h2c := h₂.1.continuous
  have hBc := Bt_continuous H hF hF' p
  have hph : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => phase D x.1 p x.2 := by
    unfold phase; fun_prop
  have hcont : Continuous (fun x : (ℝ × ℝ) × (ℝ × ℝ) => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) *
      (Bt D F F' (p, x.2) * Complex.exp (Complex.I * (phase D x.1 p x.2 : ℂ)))) := by
    have hB2 : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => Bt D F F' (p, x.2) := hBc.comp continuous_snd
    fun_prop
  refine hb.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Complex.norm_exp_I_mul_ofReal, mul_one]

theorem test_product_tau_fourier_integral (w₁ w₂ : ℝ → ℝ) (a b : ℝ) :
    (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ))) =
      om w₁ a * om w₂ (-b) := by
  unfold om
  rw [Measure.volume_eq_prod, ← integral_prod_mul]
  congr 1
  funext τ
  have : Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((τ.1 * a : ℝ) : ℂ)) * Complex.exp (Complex.I * ((τ.2 * -b : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [this]
  push_cast
  ring

theorem tau_integral_fourier_form (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (p : SS k r) :
    (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Gt D F F' τ p) =
      ∫ t : ℝ × ℝ, Bt D F F' (p, t) *
        (om w₁ (t.1 * lam k r D.z (Matrix.of p.1.2)) * om w₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2)))) := by
  simp_rw [Gt_eq H hF hF', ← integral_const_mul]
  rw [integral_integral_swap (integrable_test_weighted_phase_product H hF hF' h₁ h₂ p)]
  congr 1
  funext t
  rw [← test_product_tau_fourier_integral, ← integral_const_mul]
  congr 1
  funext τ
  have : phase D τ p t = τ.1 * (t.1 * lam k r D.z (Matrix.of p.1.2)) -
      τ.2 * (t.2 * lam k r D.z' (Matrix.of p.2.2)) := by
    unfold phase; ring
  rw [this]
  ring

theorem avg1 (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * betaInfTau D τ F F') =
      ∫ p : SS k r, (∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 *
        (om w₁ (t.1 * lam k r D.z (Matrix.of p.1.2)) * om w₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2))))) ∂D.μSS := by
  have := sigmaFinite_μSS D
  simp_rw [betaInfTau_eq H hF hF', ← integral_const_mul]
  rw [integral_integral_swap (joint_weighted_integrable H hF hF' h₁ h₂)]
  apply integral_congr_ae
  filter_upwards [ae_inSS D] with p hp
  rw [tau_integral_fourier_form H hF hF' h₁ h₂ p]
  simp_rw [Bt_eq D F F' hp]

end avg1

section avg2pre

theorem norm_exp_I_mul_ofReal_eq_one (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

theorem test_function_integrable {w : ℝ → ℝ} (hw : IsTest w) : Integrable w :=
  hw.1.continuous.integrable_of_hasCompactSupport hw.2.1

theorem test_function_fourier_continuous {w : ℝ → ℝ} (hw : IsTest w) : Continuous (om w) := by
  unfold om
  refine continuous_of_dominated (bound := fun τ => ‖w τ‖) ?_ ?_ (test_function_integrable hw).norm ?_
  · intro x
    have hc : Continuous fun τ : ℝ => (w τ : ℂ) * Complex.exp (Complex.I * ((τ * x : ℝ) : ℂ)) := by
      have := hw.1.continuous
      fun_prop
    exact hc.aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun τ => ?_
    rw [norm_mul, norm_exp_I_mul_ofReal_eq_one, mul_one, Complex.norm_real]
  · refine Filter.Eventually.of_forall fun τ => ?_
    fun_prop

theorem rpow_neg_two_eq_inv_sq {u : ℝ} (hu : 0 ≤ u) : u ^ (-2 : ℝ) = (u ^ 2)⁻¹ := by
  rw [Real.rpow_neg hu, Real.rpow_two]

theorem fourier_transform_quadratic_decay {w : ℝ → ℝ} (hw : IsTest w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖om w x‖ ≤ C * (1 + |x|) ^ (-2 : ℝ) := by
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.test_function_decay w hw
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rw [rpow_neg_two_eq_inv_sq (by positivity)]
  exact (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

theorem scaled_decay_weight_bound {t : ℝ} (ht : 1 / 2 ≤ t) (x : ℝ) :
    (1 + |t * x|) ^ (-2 : ℝ) ≤ 4 * (1 + |x|) ^ (-2 : ℝ) := by
  rw [rpow_neg_two_eq_inv_sq (by positivity), rpow_neg_two_eq_inv_sq (by positivity)]
  have h0 : 0 ≤ |x| := abs_nonneg x
  have h1 : |t * x| = t * |x| := by rw [abs_mul, abs_of_nonneg (by linarith)]
  rw [h1, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 1 + |x| ≤ 2 * (1 + t * |x|) := by nlinarith
  have h3 : 0 ≤ 1 + |x| := by positivity
  nlinarith

end avg2pre

section avg2

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem dilation_action_measurable (t : ℝ × ℝ) : Measurable (dilation₂ (k := k) (r := r) t) := by
  have h1 := (BesselUnitaryEquiv.continuous_conjM (k := k) (r := r) (aDil k r t.1)).measurable
  have h2 := (BesselUnitaryEquiv.continuous_conjM (k := k) (r := r) (aDil k r t.2)).measurable
  unfold dilation₂
  exact ((measurable_fst.fst).prodMk (h1.comp measurable_fst.snd)).prodMk
    ((measurable_snd.fst).prodMk (h2.comp measurable_snd.snd))

theorem map_measure_dilation_pair_eq_smul (hJ : DilJac D) {t : ℝ × ℝ} (h1 : 0 < t.1) (h2 : 0 < t.2) :
    D.μSS.map (dilation₂ t) =
      (ENNReal.ofReal ((t.1 ^ kap k r)⁻¹) * ENNReal.ofReal ((t.2 ^ kap k r)⁻¹)) • D.μSS := by
  have := haar_sigmaFinite D.haarW
  have := haar_sigmaFinite D.haarN
  have := haar_sigmaFinite D.haarW'
  have c1 := (BesselUnitaryEquiv.continuous_conjM (k := k) (r := r) (aDil k r t.1)).measurable
  have c2 := (BesselUnitaryEquiv.continuous_conjM (k := k) (r := r) (aDil k r t.2)).measurable
  have e : dilation₂ (k := k) (r := r) t =
      Prod.map (Prod.map id (conjM (aDil k r t.1))) (Prod.map id (conjM (aDil k r t.2))) := rfl
  unfold RealPlaceData.μSS
  rw [e, ← Measure.map_prod_map _ _ (measurable_id.prodMap c1) (measurable_id.prodMap c2),
    ← Measure.map_prod_map _ _ measurable_id c1, ← Measure.map_prod_map _ _ measurable_id c2,
    Measure.map_id, Measure.map_id, hJ t.1 h1, hJ t.2 h2, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

end avg2

section avg3

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

def fourierWeightedPhase (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (w₁ w₂ : ℝ → ℝ) (p : SS k r) : ℂ :=
  om w₁ (lam k r D.z (Matrix.of p.1.2)) * om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * Ph D F F' p

theorem first_eigenvalue_continuous (D : RealPlaceData k r Wp Wq) :
    Continuous (fun p : SS k r => lam k r D.z (Matrix.of p.1.2)) :=
  (lam_continuous k r D.z).comp (continuous_snd.comp continuous_fst)

theorem continuous_lambda_second_coordinate (D : RealPlaceData k r Wp Wq) :
    Continuous (fun p : SS k r => lam k r D.z' (Matrix.of p.2.2)) :=
  (lam_continuous k r D.z').comp (continuous_snd.comp continuous_snd)

theorem aestronglyMeasurable_dilation_pair_integrand (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : admitted α c F)
    (hF' : admitted α c' F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    AEStronglyMeasurable (fourierWeightedPhase D F F' w₁ w₂) D.μSS := by
  have hc : ContinuousOn (fourierWeightedPhase D F F' w₁ w₂) {p | D.inSS p} := by
    unfold fourierWeightedPhase
    refine ContinuousOn.mul (Continuous.continuousOn ?_) (ph_continuousOn H hF hF')
    exact ((test_function_fourier_continuous h₁).comp (first_eigenvalue_continuous D)).mul
      ((test_function_fourier_continuous h₂).comp (continuous_lambda_second_coordinate D).neg)
  have := hc.aestronglyMeasurable (μ := D.μSS) (measurableSet_inSS D)
  have hr : D.μSS.restrict {p | D.inSS p} = D.μSS := Measure.restrict_eq_self_of_ae_mem (ae_inSS D)
  rwa [hr] at this

theorem fourier_weighted_phase_integrable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : admitted α c F)
    (hF' : admitted α c' F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fourierWeightedPhase D F F' w₁ w₂) D.μSS := by
  obtain ⟨C₁, hC₁, d₁⟩ := fourier_transform_quadratic_decay h₁
  obtain ⟨C₂, hC₂, d₂⟩ := fourier_transform_quadratic_decay h₂
  obtain ⟨K, hK, hb⟩ := ph_bound H
  have hc := admissible_constant_nonneg hF
  have hc' := admissible_constant_nonneg hF'
  refine Integrable.mono' ((xi_integrable H).const_mul (C₁ * C₂ * (K * c * c'))) (aestronglyMeasurable_dilation_pair_integrand H hF hF' h₁ h₂) ?_
  filter_upwards [ae_inSS D] with p hp
  unfold fourierWeightedPhase
  rw [norm_mul, norm_mul]
  have e1 := d₁ (lam k r D.z (Matrix.of p.1.2))
  have e2 := d₂ (-lam k r D.z' (Matrix.of p.2.2))
  rw [abs_neg] at e2
  have e3 := hb F F' c c' hF hF' p hp
  have hX := XX_nonneg Ξ p
  calc ‖om w₁ (lam k r D.z (Matrix.of p.1.2))‖ * ‖om w₂ (-lam k r D.z' (Matrix.of p.2.2))‖ * ‖Ph D F F' p‖
      ≤ (C₁ * (1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-2 : ℝ)) *
          (C₂ * (1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-2 : ℝ)) * (K * c * c' * XX Ξ p) := by
        gcongr
    _ = C₁ * C₂ * (K * c * c') * (XX Ξ p * LL D p) := by unfold LL; ring

end avg3

section avg4

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem integral_dilation_pair_integrand_eq (H : Hyp D Ξ α) (hJ : DilJac D) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : admitted α c F) (hF' : admitted α c' F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {t : ℝ × ℝ}
    (h1 : 0 < t.1) (h2 : 0 < t.2) :
    (∫ p, fourierWeightedPhase D F F' w₁ w₂ (dilation₂ t p) ∂D.μSS) =
      ((((t.1 * t.2) ^ kap k r)⁻¹ : ℝ) : ℂ) * ∫ p, fourierWeightedPhase D F F' w₁ w₂ p ∂D.μSS := by
  have hm := map_measure_dilation_pair_eq_smul hJ h1 h2
  have e : (∫ q, fourierWeightedPhase D F F' w₁ w₂ q ∂(D.μSS.map (dilation₂ t))) = ∫ p, fourierWeightedPhase D F F' w₁ w₂ (dilation₂ t p) ∂D.μSS :=
    integral_map (dilation_action_measurable t).aemeasurable
      (by rw [hm]; exact (aestronglyMeasurable_dilation_pair_integrand H hF hF' h₁ h₂).smul_measure _)
  rw [← e, hm, integral_smul_measure, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul, mul_pow, mul_inv]

def weightedPhaseJointIntegrand (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (w₁ w₂ : ℝ → ℝ)
    (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Bt D F F' q * (om w₁ (q.2.1 * lam k r D.z (Matrix.of q.1.1.2)) *
    om w₂ (-(q.2.2 * lam k r D.z' (Matrix.of q.1.2.2))))

theorem second_integrand_integrable (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (weightedPhaseJointIntegrand D F F' w₁ w₂) (D.μSS.prod volume) := by
  have := sigmaFinite_μSS D
  obtain ⟨C₁, hC₁, d₁⟩ := fourier_transform_quadratic_decay h₁
  obtain ⟨C₂, hC₂, d₂⟩ := fourier_transform_quadratic_decay h₂
  obtain ⟨K, hK, hb⟩ := Bt_bound H
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hbox : Integrable (Set.indicator (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) (fun _ : ℝ × ℝ => (1 : ℝ))) :=
    (continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  have hdom := ((xi_integrable H).const_mul (16 * (C₁ * C₂) * (K * c * c'))).mul_prod hbox
  have hmeas : AEStronglyMeasurable (weightedPhaseJointIntegrand D F F' w₁ w₂) (D.μSS.prod volume) := by
    unfold weightedPhaseJointIntegrand
    refine ((Bt_measurable H hF hF').mul (Continuous.stronglyMeasurable ?_)).aestronglyMeasurable
    exact ((test_function_fourier_continuous h₁).comp ((continuous_fst.comp continuous_snd).mul
        ((first_eigenvalue_continuous D).comp continuous_fst))).mul
      ((test_function_fourier_continuous h₂).comp ((continuous_snd.comp continuous_snd).mul
        ((continuous_lambda_second_coordinate D).comp continuous_fst)).neg)
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨p, t⟩ := q
  have hX := XX_nonneg Ξ p
  by_cases ht : t ∈ Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2
  · simp only [Set.indicator_of_mem ht, mul_one]
    unfold weightedPhaseJointIntegrand
    rw [norm_mul, norm_mul]
    have e1 := (d₁ (t.1 * lam k r D.z (Matrix.of p.1.2))).trans
      (mul_le_mul_of_nonneg_left (scaled_decay_weight_bound ht.1.1 _) hC₁)
    have e2 := d₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2)))
    rw [abs_neg] at e2
    have e2' := e2.trans (mul_le_mul_of_nonneg_left (scaled_decay_weight_bound ht.2.1 _) hC₂)
    have e3 := hb F F' c c' hF hF' p t
    calc ‖Bt D F F' (p, t)‖ * (‖om w₁ (t.1 * lam k r D.z (Matrix.of p.1.2))‖ *
          ‖om w₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2)))‖)
        ≤ (K * c * c' * XX Ξ p) * ((C₁ * (4 * (1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-2 : ℝ))) *
            (C₂ * (4 * (1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-2 : ℝ)))) := by
          gcongr
      _ = 16 * (C₁ * C₂) * (K * c * c') * (XX Ξ p * LL D p) := by unfold LL; ring
  · have ht' : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2 := fun h =>
      ht ⟨Set.Ioo_subset_Icc_self h.1, Set.Ioo_subset_Icc_self h.2⟩
    simp only [Set.indicator_of_notMem ht, mul_zero]
    unfold weightedPhaseJointIntegrand
    rw [Bt_zero D F F' p ht', zero_mul, norm_zero]

end avg4

section avg5

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}

theorem cutoff_vanishes_outside_interval (D : RealPlaceData k r Wp Wq) {t : ℝ} (ht : t ∉ Set.Ioo (1 / 2 : ℝ) 2) : D.χ t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => ht (D.χ_supp h)

theorem integrand_slice_formula (H : Hyp D Ξ α) (hJ : DilJac D) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂)
    (t : ℝ × ℝ) :
    (∫ p, weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t) ∂D.μSS) =
      ((D.χ t.1 * D.χ t.2 : ℝ) : ℂ) * ∫ p, fourierWeightedPhase D F F' w₁ w₂ p ∂D.μSS := by
  by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
  · have h1 : 0 < t.1 := lt_trans (by norm_num) ht.1.1
    have h2 : 0 < t.2 := lt_trans (by norm_num) ht.2.1
    have e : ∀ᵐ p ∂D.μSS, weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t) =
        ((D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ) : ℂ) * fourierWeightedPhase D F F' w₁ w₂ (dilation₂ t p) := by
      filter_upwards [ae_inSS D] with p hp
      obtain ⟨l1, l2⟩ := lam_dil H.dilN D hp h1 h2
      have l1' : lam k r D.z (Matrix.of (dilation₂ t p).1.2) = t.1 * lam k r D.z (Matrix.of p.1.2) := l1
      have l2' : lam k r D.z' (Matrix.of (dilation₂ t p).2.2) = t.2 * lam k r D.z' (Matrix.of p.2.2) := l2
      unfold weightedPhaseJointIntegrand fourierWeightedPhase
      rw [Bt_eq D F F' hp, l1', l2']
      unfold regBracket
      ring
    rw [integral_congr_ae e, integral_const_mul,
      integral_dilation_pair_integrand_eq H hJ (admissible_of_weighted hF) (admissible_of_weighted hF') h₁ h₂ h1 h2, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    have hpos : (t.1 * t.2) ^ kap k r ≠ 0 := by positivity
    field_simp
  · have hz : D.χ t.1 * D.χ t.2 = 0 := by
      by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
      · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h => ht ⟨h1, h⟩
        rw [cutoff_vanishes_outside_interval D h2, mul_zero]
      · rw [cutoff_vanishes_outside_interval D h1, zero_mul]
    have e : ∀ p, weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t) = 0 := fun p => by
      unfold weightedPhaseJointIntegrand
      rw [Bt_zero D F F' p ht, zero_mul]
    simp only [e, integral_zero, hz, Complex.ofReal_zero, zero_mul]

theorem integral_cutoff_product_eq_one (D : RealPlaceData k r Wp Wq) : (∫ t : ℝ × ℝ, ((D.χ t.1 * D.χ t.2 : ℝ) : ℂ)) = 1 := by
  rw [integral_complex_ofReal]
  have : (∫ t : ℝ × ℝ, D.χ t.1 * D.χ t.2) = (∫ x, D.χ x) * ∫ y, D.χ y :=
    integral_prod_mul (μ := volume) (ν := volume) D.χ D.χ
  rw [this, D.χ_int]
  simp

theorem regAverage_of_hyp (H : Hyp D Ξ α) (hJ : DilJac D) : RegAverage D α := by
  intro F F' ⟨c, hc⟩ ⟨c', hc'⟩ w₁ w₂ h₁ h₂
  have hF := admissible_weighted_of_bound hc
  have hF' := admissible_weighted_of_bound hc'
  have := sigmaFinite_μSS D
  refine ⟨fourier_weighted_phase_integrable H (admissible_of_weighted hF) (admissible_of_weighted hF') h₁ h₂, ?_⟩
  rw [avg1 H hF hF' h₁ h₂]
  have e1 : (∫ p : SS k r, (∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 *
        (om w₁ (t.1 * lam k r D.z (Matrix.of p.1.2)) * om w₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2))))) ∂D.μSS) =
      ∫ p : SS k r, (∫ t : ℝ × ℝ, weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t)) ∂D.μSS := by
    refine integral_congr_ae ?_
    filter_upwards [ae_inSS D] with p hp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show _ = weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t)
    unfold weightedPhaseJointIntegrand
    rw [Bt_eq D F F' hp]
  rw [e1, integral_integral_swap (f := fun p t => weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t))
    (second_integrand_integrable H hF hF' h₁ h₂)]
  simp only [integrand_slice_formula H hJ hF hF' h₁ h₂]
  rw [integral_mul_const, integral_cutoff_product_eq_one, one_mul]
  rfl

end avg5

section top

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem top_ph_zero [Subsingleton (Wq →L[ℂ] Wp)] (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp))
    (p : SS k r) : Ph D F F' p = 0 := by
  unfold Ph
  have : ∀ g : Mt k r, hsInner (rho D p F (Matrix.of g)) (F' (Matrix.of g)) = 0 := by
    intro g
    have h0 : F' (Matrix.of g) = 0 := Subsingleton.elim _ _
    rw [h0]
    unfold hsInner hsVec
    simp [PiLp.inner_apply]
  simp [this]

theorem top_beta_zero [Subsingleton (Wq →L[ℂ] Wp)] (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ)
    (F F' : Mat k r → (Wq →L[ℂ] Wp)) : betaInfTau D τ F F' = 0 := by
  have hb : ∀ p, regBracket D F F' p = fun _ _ => 0 := by
    intro p; funext x y; unfold regBracket; rw [top_ph_zero]; simp
  have ho : ∀ x y, oneMinusDD (fun _ _ => (0 : ℂ)) x y = 0 := by
    intro x y; unfold oneMinusDD; simp
  unfold betaInfTau
  simp [hb, ho]

theorem top_hyp (hN : DilN) (hU : DilUW) [Nontrivial (Wq →L[ℂ] Wp)] {D : RealPlaceData k r Wp Wq}
    {Ξ : Mat k r → NNReal} {A : ℝ} (hA : AB k r ≤ A) (h1 : CoefBound D Ξ A) (h2 : XiInt D Ξ 2) : Hyp D Ξ A where
  α_nonneg := le_trans (B2.AB_nonneg k r) hA
  coef := h1
  xi := h2
  T0 := exists_norm_eq (Wq →L[ℂ] Wp) zero_le_one
  dilN := hN
  dilUW := hU

theorem top_regBound (hN : DilN) (hU : DilUW) : StepRegBound := by
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hA h1 h2
  rcases subsingleton_or_nontrivial (Wq →L[ℂ] Wp) with hs | hn
  · refine ⟨fun τ₀ _ => ⟨0, Set.univ, univ_mem, fun τ _ F F' c c' _ _ => ?_⟩, fun F F' _ _ => ?_,
      fun τ _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [top_beta_zero]; simp
    · simp only [top_beta_zero]; exact continuousOn_const
    all_goals intros; simp only [top_beta_zero]; simp
  · exact regBound_of_hyp (top_hyp hN hU hA h1 h2)

theorem top_regAverage (hN : DilN) (hU : DilUW) : StepRegAverage := by
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hA h1 h2 hJ
  rcases subsingleton_or_nontrivial (Wq →L[ℂ] Wp) with hs | hn
  · intro F F' _ _ w₁ w₂ _ _
    simp only [top_beta_zero, top_ph_zero]
    simp
  · exact regAverage_of_hyp (top_hyp hN hU hA h1 h2) hJ

end top

end Formalism.FourierDecayAlt.P.B6

namespace Formalism.FourierDecayAlt.P

theorem regularized_beta_bound_continuity_sesquilinear : Formalism.FourierDecayAlt.B.StepRegBound := B6.top_regBound dilation_unipotent_measure dilation_unipotent_weyl_measure

theorem regularised_average_identity : Formalism.FourierDecayAlt.B.StepRegAverage := B6.top_regAverage dilation_unipotent_measure dilation_unipotent_weyl_measure

end Formalism.FourierDecayAlt.P
