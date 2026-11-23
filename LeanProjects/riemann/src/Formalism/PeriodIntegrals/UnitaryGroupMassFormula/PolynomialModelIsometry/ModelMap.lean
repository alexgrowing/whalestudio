import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.IsPolyMon

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

namespace MMap

lemma eval_aeval_eq {σ τ : Type*} (y : τ → ℂ) (g : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ) :
    eval y (aeval g f) = eval (fun i => eval y (g i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

lemma poly_ext {N : ℕ} {p q : MvPolynomial (Fin N × Fin N) ℂ}
    (h : ∀ A : Matrix (Fin N) (Fin N) ℂ, evM A p = evM A q) : p = q := by
  apply MvPolynomial.funext
  intro x
  have := h (Matrix.of fun i j => x (i, j))
  simpa [evM] using this

lemma evM_add {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (p + q) = evM A p + evM A q := by simp [evM]

lemma evM_smul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (c • p) = c * evM A p := by
  rw [evM, evM, smul_eq_C_mul, eval_mul, eval_C]

lemma evM_C_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (C c * p) = c * evM A p := by
  rw [evM, evM, eval_mul, eval_C]

lemma evM_rename_swap {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (rename Prod.swap q) = evM Aᵀ q := by
  simp only [evM, eval_rename]
  rfl

lemma evM_rowAct {N : ℕ} (g A : Matrix (Fin N) (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (rowAct ℂ (n := N) g f) = evM (g * A) f := by
  unfold rowAct evM
  rw [eval_aeval_eq]
  refine congrArg (fun y => eval y f) (funext fun v => ?_)
  simp [Matrix.mul_apply]

lemma evM_colAdd {N : ℕ} (l j : Fin N) (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (colAdd ℂ (r := N) l j c f) = evM (A * (1 + Matrix.single l j c)) f := by
  unfold colAdd evM
  rw [eval_aeval_eq]
  refine congrArg (fun y => eval y f) (funext fun v => ?_)
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  split_ifs with h
  · simp [Matrix.mul_apply, Matrix.single_apply, h, mul_comm]
  · have h' : j ≠ v.2 := fun e => h e.symm
    simp [Matrix.mul_apply, Matrix.single_apply, h']

lemma evM_scale {N : ℕ} (t : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (aeval (fun v : Fin N × Fin N => C (t v.2) * X v) f) = evM (A * Matrix.diagonal t) f := by
  unfold evM
  rw [eval_aeval_eq]
  refine congrArg (fun y => eval y f) (funext fun v => ?_)
  simp [Matrix.mul_diagonal, mul_comm]

lemma aeval_scale_monomial {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℂ) (u : σ →₀ ℕ) (c : ℂ) :
    aeval (fun v : σ => C (w v) * X v) (monomial u c) = monomial u (c * ∏ v, w v ^ u v) := by
  rw [aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (w v) : MvPolynomial σ ℂ) ^ e) = C (u.prod fun v e => w v ^ e) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hC, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), monomial_eq, C_mul, algebraMap_eq]
  ring

lemma coeff_scale {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (aeval (fun v : σ => C (w v) * X v) f) = coeff m f * ∏ v, w v ^ m v := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]

lemma prod_exp {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (θ : Fin N → ℝ) :
    ∏ v : Fin N × Fin N, Complex.exp ((θ v.2 : ℂ) * Complex.I) ^ m v =
      Complex.exp (((∑ v : Fin N × Fin N, (m v : ℝ) * θ v.2 : ℝ) : ℂ) * Complex.I) := by
  simp_rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => by ring

lemma real_eq_of_exp {d c : ℝ}
    (h : ∀ τ : ℝ, Complex.exp (((τ * d : ℝ) : ℂ) * Complex.I) = Complex.exp (((τ * c : ℝ) : ℂ) * Complex.I)) :
    d = c := by
  by_contra hne
  have hk : d - c ≠ 0 := sub_ne_zero.mpr hne
  have h1 := h (Real.pi / (d - c))
  have h2 : Complex.exp (((Real.pi / (d - c) * d : ℝ) : ℂ) * Complex.I -
      ((Real.pi / (d - c) * c : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 : ((Real.pi / (d - c) * d : ℝ) : ℂ) * Complex.I - ((Real.pi / (d - c) * c : ℝ) : ℂ) * Complex.I =
      (Real.pi : ℂ) * Complex.I := by
    rw [← sub_mul]
    congr 1
    rw [← Complex.ofReal_sub]
    congr 1
    field_simp
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

lemma weight_colW {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (s : Fin N) :
    Finsupp.weight (colW N N) m s = ∑ v : Fin N × Fin N, if v.2 = s then m v else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v.2 = s
  · subst h; simp [colW]
  · simp [colW, h, Ne.symm h]

section

variable {N : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {P : Matrix (Fin N) (Fin N) ℂ → (V →ₗ[ℂ] V)} (hP : IsPolyMon P) (v0 : V)

def Fq (x : V) : MvPolynomial (Fin N × Fin N) ℂ :=
  rename Prod.swap (Classical.choose (hP.poly x v0))

lemma evM_Fq (x : V) (A : Matrix (Fin N) (Fin N) ℂ) : evM A (Fq hP v0 x) = ⟪v0, P Aᵀ x⟫_ℂ := by
  unfold Fq
  rw [evM_rename_swap]
  exact Classical.choose_spec (hP.poly x v0) Aᵀ

def Fl : V →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := Fq hP v0
  map_add' x y := poly_ext fun A => by
    rw [evM_add, evM_Fq, evM_Fq, evM_Fq, map_add, inner_add_right]
  map_smul' c x := poly_ext fun A => by
    rw [RingHom.id_apply, evM_smul, evM_Fq, evM_Fq, map_smul, inner_smul_right]

lemma Fl_apply (x : V) : Fl hP v0 x = Fq hP v0 x := rfl

lemma Fq_intertwine (g : Matrix (Fin N) (Fin N) ℂ) (x : V) :
    Fq hP v0 (P g x) = rowAct ℂ (n := N) gᵀ (Fq hP v0 x) := poly_ext fun A => by
  rw [evM_rowAct, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.transpose_transpose, hP.mul,
    LinearMap.comp_apply]

lemma Fq_colAdd
    (hlow : ∀ a b : Fin N, a < b → ∀ (c : ℂ) (x : V), ⟪v0, P (1 + Matrix.single b a c) x⟫_ℂ = ⟪v0, x⟫_ℂ)
    (l j : Fin N) (hlj : l < j) (c : ℂ) (x : V) :
    colAdd ℂ (r := N) l j c (Fq hP v0 x) = Fq hP v0 x := poly_ext fun A => by
  rw [evM_colAdd, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, hP.mul, LinearMap.comp_apply, hlow l j hlj]

lemma Fq_scale (μ : Fin N → ℤ) (K : ℕ)
    (htor : ∀ (θ : Fin N → ℝ) (x : V), ⟪v0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪v0, x⟫_ℂ)
    (θ : Fin N → ℝ) (x : V) :
    aeval (fun v : Fin N × Fin N => C (Complex.exp ((θ v.2 : ℂ) * Complex.I)) * X v) (Fq hP v0 x) =
      C (Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I)) * Fq hP v0 x :=
  poly_ext fun A => by
    rw [evM_scale (fun s => Complex.exp ((θ s : ℂ) * Complex.I)), evM_C_mul, evM_Fq, evM_Fq, Matrix.transpose_mul, Matrix.diagonal_transpose, ← htor θ,
      hP.mul, LinearMap.comp_apply]
    rfl

lemma Fq_deg (μ : Fin N → ℤ) (K : ℕ)
    (htor : ∀ (θ : Fin N → ℝ) (x : V), ⟪v0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪v0, x⟫_ℂ)
    (x : V) (m : Fin N × Fin N →₀ ℕ) (hm : coeff m (Fq hP v0 x) ≠ 0) (s : Fin N) :
    (((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ)) : ℤ) = μ s + K := by
  have key : ((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ) : ℝ) = (μ s : ℝ) + K := by
    apply real_eq_of_exp
    intro τ
    have h1 := congrArg (coeff m) (Fq_scale hP v0 μ K htor (fun s' => if s' = s then τ else 0) x)
    rw [coeff_scale, coeff_C_mul, mul_comm (Complex.exp _), prod_exp m (fun s' => if s' = s then τ else 0)] at h1
    have h2 := mul_left_cancel₀ hm h1
    have e1 : (∑ v : Fin N × Fin N, (m v : ℝ) * (if v.2 = s then τ else 0)) =
        τ * ((∑ v : Fin N × Fin N, if v.2 = s then m v else 0 : ℕ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> ring
    have e2 : (∑ a : Fin N, ((μ a : ℝ) + K) * (if a = s then τ else 0)) = τ * ((μ s : ℝ) + K) := by
      simp [mul_ite, Finset.sum_ite_eq']
      ring
    rw [e1, e2] at h2
    exact h2
  exact_mod_cast key

end

end MMap

open MMap in
theorem model_map_equivariance : ModelMap := by
  intro N V _ _ _ P v0 μ K hP hv0 htor hlow
  have hF0 : Fq hP v0 v0 ≠ 0 := by
    intro h
    have h1 := evM_Fq hP v0 v0 1
    rw [h, Matrix.transpose_one, hP.one, LinearMap.id_apply] at h1
    have h2 : evM (1 : Matrix (Fin N) (Fin N) ℂ) (0 : MvPolynomial (Fin N × Fin N) ℂ) = 0 := by simp [evM]
    rw [h2] at h1
    exact hv0 (inner_self_eq_zero.mp h1.symm)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hF0
  have hnn : ∀ s, 0 ≤ μ s + K := fun s => by
    rw [← Fq_deg hP v0 μ K htor v0 m0 hm0 s]
    positivity
  refine ⟨fun s => (μ s + K).toNat, Fl hP v0, fun s => Int.toNat_of_nonneg (hnn s), ?_, hF0, ?_⟩
  · intro x
    rw [Fl_apply, dualWeylPoint ℂ N N _ _]
    refine ⟨?_, fun l j hlj c => Fq_colAdd hP v0 hlow l j hlj c x⟩
    intro m hm
    funext s
    rw [weight_colW]
    have h1 := Fq_deg hP v0 μ K htor x m hm s
    have h2 := Int.toNat_of_nonneg (hnn s)
    omega
  · intro g x
    rw [Fl_apply, Fl_apply]
    exact Fq_intertwine hP v0 g x

end PI.WMI
