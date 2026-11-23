import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt

noncomputable section

open MeasureTheory MvPolynomial
open scoped Matrix

namespace PositivityTheory.Rg.Sw.FFTSteps.CA

variable {m n : ℕ}

def pt (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = eval (pt x) P := rfl

def subR (u : Matrix (Fin m) (Fin m) ℂ) : PX m n →ₐ[ℂ] PX m n :=
  aeval (fun k : Fin m × Fin n × Bool => if k.2.2 then ∑ b, C (star (u k.1 b)) * X (b, k.2.1, true)
    else ∑ b, C (u k.1 b) * X (b, k.2.1, false))

def act (u : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun a i => ∑ b, u a b * x b i

theorem subR_C (u : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) : subR (n := n) u (C c) = C c := by
  simp [subR, algebraMap_eq]

theorem subR_X_false (u : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) :
    subR u (X (a, i, false)) = ∑ b, C (u a b) * X (b, i, false) := by
  simp [subR]

theorem subR_X_true (u : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) :
    subR u (X (a, i, true)) = ∑ b, C (star (u a b)) * X (b, i, true) := by
  simp [subR]

theorem eval_pt_var (u : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) :
    eval (pt x) (subR u (X k)) = pt (act u x) k := by
  rcases k with ⟨a, i, _ | _⟩
  · rw [subR_X_false]; simp [pt, act]
  · rw [subR_X_true]; simp [pt, act, star_sum]

theorem evX_subR (u : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    evX (subR u P) x = evX P (act u x) := by
  induction P using MvPolynomial.induction_on
  next c => simp [evX_eq]
  next p q hp hq => simp only [evX_eq, map_add] at *; rw [hp, hq]
  next p k hp =>
    simp only [evX_eq, map_mul] at *
    rw [hp, eval_pt_var, eval_X]

theorem subR_comp (v w : Matrix (Fin m) (Fin m) ℂ) : (subR (n := n) v).comp (subR w) = subR (w * v) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨a, i, _ | _⟩
  · simp only [AlgHom.comp_apply, subR_X_false, map_sum, map_mul, subR_C]
    simp only [Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul, ← mul_assoc, ← C_mul]
    exact Finset.sum_comm
  · simp only [AlgHom.comp_apply, subR_X_true, map_sum, map_mul, subR_C]
    simp only [Finset.mul_sum, Matrix.mul_apply, star_sum, star_mul', map_sum, Finset.sum_mul, ← mul_assoc, ← C_mul]
    exact Finset.sum_comm

theorem subR_subR (v w : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : subR v (subR w P) = subR (w * v) P := by
  rw [← AlgHom.comp_apply, subR_comp]

def sq (x : Fin m → Fin n → ℂ) : ℝ := ∑ a, ∑ i, ‖x a i‖ ^ 2

theorem ofReal_sum_sq (z : Fin m → ℂ) : ((∑ a, ‖z a‖ ^ 2 : ℝ) : ℂ) = star z ⬝ᵥ z := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

theorem sum_sq_mulVec (u : Matrix (Fin m) (Fin m) ℂ) (hu : uᴴ * u = 1) (z : Fin m → ℂ) :
    ∑ a, ‖(u *ᵥ z) a‖ ^ 2 = ∑ a, ‖z a‖ ^ 2 := by
  have h : star (u *ᵥ z) ⬝ᵥ (u *ᵥ z) = star z ⬝ᵥ z := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hu, Matrix.vecMul_one]
  rw [← ofReal_sum_sq, ← ofReal_sum_sq] at h
  exact_mod_cast h

theorem sq_act (u : Matrix (Fin m) (Fin m) ℂ) (hu : uᴴ * u = 1) (x : Fin m → Fin n → ℂ) : sq (act u x) = sq x := by
  unfold sq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a i => ‖x a i‖ ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact sum_sq_mulVec u hu (fun b => x b i)

theorem gs_eq (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = Complex.exp (-(c * sq x : ℝ)) := rfl

theorem gs_act (c : ℝ) (u : Matrix (Fin m) (Fin m) ℂ) (hu : uᴴ * u = 1) (x : Fin m → Fin n → ℂ) :
    gs c (act u x) = gs c x := by
  rw [gs_eq, gs_eq, sq_act u hu]

def actL (u : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ) where
  toFun := act u
  map_add' x y := by funext a i; simp [act, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by funext a i; simp [act, Finset.mul_sum, mul_left_comm]

theorem det_actL (u : Matrix (Fin m) (Fin m) ℂ) : LinearMap.det (actL (n := n) u) = u.det ^ n := by
  let e := LinearEquiv.curry ℂ ℂ (Fin m) (Fin n)
  have hL : actL (n := n) u = (e : _ →ₗ[ℂ] _) ∘ₗ Matrix.toLin' (Matrix.kroneckerMap (· * ·) u (1 : Matrix (Fin n) (Fin n) ℂ)) ∘ₗ
      (e.symm : _ →ₗ[ℂ] _) := by
    apply LinearMap.ext; intro x; funext a i
    simp [actL, act, e, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [hL, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker]
  simp

theorem mp_act (u : Matrix (Fin m) (Fin m) ℂ) (hu : uᴴ * u = 1) :
    MeasurePreserving (act (n := n) u) volume volume := by
  set f : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := (actL (n := n) u).restrictScalars ℝ with hf
  have hn : ((Complex.normSq u.det : ℝ) : ℂ) = 1 := by
    have h := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  have hn' : Complex.normSq u.det = 1 := by exact_mod_cast hn
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, det_actL, map_pow, Algebra.norm_complex_apply, hn', one_pow]
  have hfe : (act (n := n) u) = ⇑f := rfl
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  rw [hfe]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

theorem continuous_pt (k : Fin m × Fin n × Bool) : Continuous fun x : Fin m → Fin n → ℂ => pt x k := by
  rcases k with ⟨a, i, _ | _⟩
  · simp only [pt, Bool.false_eq_true, if_false]; fun_prop
  · simp only [pt, if_true]; fun_prop

theorem continuous_evX (P : PX m n) : Continuous (evX P) := by
  induction P using MvPolynomial.induction_on
  next c =>
    have : evX (C c : PX m n) = fun _ => c := by funext x; simp [evX_eq]
    rw [this]; exact continuous_const
  next p q hp hq =>
    have : evX (p + q) = fun x => evX p x + evX q x := by funext x; simp [evX_eq]
    rw [this]; exact hp.add hq
  next p k hp =>
    have : evX (p * X k) = fun x => evX p x * pt x k := by funext x; simp [evX_eq]
    rw [this]; exact hp.mul (continuous_pt k)

theorem continuous_gs (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  unfold gs; fun_prop

theorem sq_nonneg' (x : Fin m → Fin n → ℂ) : 0 ≤ sq x := by
  unfold sq; positivity

theorem norm_le_sq (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) : ‖x a i‖ ^ 2 ≤ sq x := by
  unfold sq
  calc ‖x a i‖ ^ 2 ≤ ∑ i', ‖x a i'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ‖x a i'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
    _ ≤ ∑ a', ∑ i', ‖x a' i'‖ ^ 2 :=
        Finset.single_le_sum (f := fun a' => ∑ i', ‖x a' i'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)

theorem coord_bound {δ : ℝ} (hδ : 0 < δ) (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    ‖x a i‖ ≤ (1 + 1 / δ) * Real.exp (δ * sq x) := by
  have h1 : ‖x a i‖ ≤ 1 + ‖x a i‖ ^ 2 := by nlinarith [sq_nonneg (‖x a i‖ - 1), norm_nonneg (x a i)]
  have h2 := norm_le_sq x a i
  have h3 : 1 + δ * sq x ≤ Real.exp (δ * sq x) := by linarith [Real.add_one_le_exp (δ * sq x)]
  have h4 : 0 ≤ sq x := sq_nonneg' x
  have h5 : 1 ≤ Real.exp (δ * sq x) := Real.one_le_exp (by positivity)
  have h6 : sq x ≤ Real.exp (δ * sq x) / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  calc ‖x a i‖ ≤ 1 + sq x := by linarith
    _ ≤ Real.exp (δ * sq x) + Real.exp (δ * sq x) / δ := by linarith
    _ = (1 + 1 / δ) * Real.exp (δ * sq x) := by ring

theorem exp_bound (P : PX m n) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x, ‖evX P x‖ ≤ C * Real.exp (ε * sq x) := by
  induction P using MvPolynomial.induction_on
  next c =>
    intro ε hε
    refine ⟨‖c‖, fun x => ?_⟩
    have : 1 ≤ Real.exp (ε * sq x) := Real.one_le_exp (mul_nonneg hε.le (sq_nonneg' x))
    simp only [evX_eq, eval_C]
    nlinarith [norm_nonneg c]
  next p q hp hq =>
    intro ε hε
    obtain ⟨C1, h1⟩ := hp ε hε
    obtain ⟨C2, h2⟩ := hq ε hε
    refine ⟨C1 + C2, fun x => ?_⟩
    have : evX (p + q) x = evX p x + evX q x := by simp [evX_eq]
    rw [this]
    calc ‖evX p x + evX q x‖ ≤ ‖evX p x‖ + ‖evX q x‖ := norm_add_le _ _
      _ ≤ C1 * Real.exp (ε * sq x) + C2 * Real.exp (ε * sq x) := add_le_add (h1 x) (h2 x)
      _ = (C1 + C2) * Real.exp (ε * sq x) := by ring
  next p k hp =>
    intro ε hε
    obtain ⟨C1, h1⟩ := hp (ε / 2) (by linarith)
    refine ⟨max C1 0 * (1 + 1 / (ε / 2)), fun x => ?_⟩
    have e : evX (p * X k) x = evX p x * pt x k := by simp [evX_eq]
    have hk : ‖pt x k‖ ≤ (1 + 1 / (ε / 2)) * Real.exp (ε / 2 * sq x) := by
      rcases k with ⟨a, i, _ | _⟩
      · have hb := coord_bound (δ := ε / 2) (by linarith) x a i
        simp only [pt, Bool.false_eq_true, if_false]
        exact hb
      · have hb := coord_bound (δ := ε / 2) (by linarith) x a i
        simp only [pt, if_true, norm_star]
        exact hb
    have hp' : ‖evX p x‖ ≤ max C1 0 * Real.exp (ε / 2 * sq x) :=
      (h1 x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    rw [e, norm_mul]
    calc ‖evX p x‖ * ‖pt x k‖ ≤ (max C1 0 * Real.exp (ε / 2 * sq x)) * ((1 + 1 / (ε / 2)) * Real.exp (ε / 2 * sq x)) :=
          mul_le_mul hp' hk (norm_nonneg _) (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)
      _ = max C1 0 * (1 + 1 / (ε / 2)) * Real.exp (ε * sq x) := by
          rw [show ε * sq x = ε / 2 * sq x + ε / 2 * sq x by ring, Real.exp_add]; ring

theorem integral_gauss_plane {b : ℝ} (hb : 0 < b) : ∫ z : ℂ, Real.exp (-(b * ‖z‖ ^ 2)) = Real.pi / b := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hb
  simp only [neg_mul] at h
  rw [h, Complex.finrank_real_complex]
  norm_num

theorem integrable_gauss_plane {b : ℝ} (hb : 0 < b) : Integrable (fun z : ℂ => Real.exp (-(b * ‖z‖ ^ 2))) := by
  by_contra h
  have h0 := integral_undef h
  rw [integral_gauss_plane hb] at h0
  exact (div_pos Real.pi_pos hb).ne' h0

theorem integrable_exp_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Fin m → Fin n → ℂ => Real.exp (-(b * sq x))) := by
  have hin : Integrable (fun y : Fin n → ℂ => ∏ i, Real.exp (-(b * ‖y i‖ ^ 2))) := by
    have := Integrable.fintype_prod (ι := Fin n) (E := ℂ) (f := fun _ z => Real.exp (-(b * ‖z‖ ^ 2)))
      (μ := fun _ => (volume : Measure ℂ)) (fun _ => integrable_gauss_plane hb)
    exact this
  have hout : Integrable (fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, Real.exp (-(b * ‖x a i‖ ^ 2))) := by
    have := Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (f := fun _ y => ∏ i, Real.exp (-(b * ‖y i‖ ^ 2)))
      (μ := fun _ => (volume : Measure (Fin n → ℂ))) (fun _ => hin)
    exact this
  refine hout.congr (Filter.Eventually.of_forall fun x => ?_)
  show ∏ a, ∏ i, Real.exp (-(b * ‖x a i‖ ^ 2)) = Real.exp (-(b * sq x))
  unfold sq
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem integrable_evX_gs {c : ℝ} (hc : 0 < c) (P : PX m n) : Integrable (fun x => evX P x * gs c x) := by
  obtain ⟨C, hC⟩ := exp_bound P (c / 2) (by linarith)
  refine Integrable.mono' ((integrable_exp_sq (b := c / 2) (by linarith)).const_mul C)
    ((continuous_evX P).mul (continuous_gs c)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, gs_eq, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
  calc ‖evX P x‖ * Real.exp (-(c * sq x)) ≤ C * Real.exp (c / 2 * sq x) * Real.exp (-(c * sq x)) :=
        mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le
    _ = C * Real.exp (-(c / 2 * sq x)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem mom_subR {c : ℝ} (u : Matrix (Fin m) (Fin m) ℂ) (hu : uᴴ * u = 1) (P : PX m n) :
    mom c (subR u P) = mom c P := by
  unfold mom
  simp_rw [evX_subR]
  have h : (fun x => evX P (act u x) * gs c x) = fun x => (fun y => evX P y * gs c y) (act u x) := by
    funext x; simp only; rw [gs_act c u hu]
  rw [h, ← integral_map (f := fun y => evX P y * gs c y) (mp_act u hu).measurable.aemeasurable
    ((continuous_evX P).mul (continuous_gs c)).aestronglyMeasurable, (mp_act u hu).map_eq]

end PositivityTheory.Rg.Sw.FFTSteps.CA
