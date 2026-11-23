import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ComplexHessianTransposeIsHermitian
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section
open scoped ComplexOrder
namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallHess

def hP {a b : Type} [Fintype a] [Fintype b] [DecidableEq b] (Z U V : Matrix a b ℂ) : ℝ :=
  (trace ((1 - Zᴴ * Z)⁻¹ * (Zᴴ * U + Uᴴ * Z) * (1 - Zᴴ * Z)⁻¹ * (Zᴴ * V + Vᴴ * Z))).re +
    (trace ((1 - Zᴴ * Z)⁻¹ * (Uᴴ * V + Vᴴ * U))).re

section Analysis

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {m : Type} [Fintype m] [DecidableEq m]

theorem hasDerivAt_det_line (A X : Matrix m m ℂ) (hA : IsUnit A.det) :
    HasDerivAt (fun s : ℝ => (A + s • X).det) (A.det * trace (A⁻¹ * X)) 0 := by
  have h0 : ∀ s : ℝ, (A + s • X).det = A.det * (1 + (s : ℂ) • (A⁻¹ * X)).det := by
    intro s
    rw [← Matrix.det_mul]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
    ext a b; simp
  set M := A⁻¹ * X
  set g := (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)).divX.divX
  have h1 : HasDerivAt (fun r : ℂ => 1 + trace M * r + g.eval r * r ^ 2) (trace M) ((0 : ℝ) : ℂ) := by
    have h := ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul (trace M)).const_add 1
    have h2 := (g.hasDerivAt ((0 : ℝ) : ℂ)).mul ((hasDerivAt_id ((0 : ℝ) : ℂ)).pow 2)
    have h3 : HasDerivAt (fun r : ℂ => 1 + trace M * r + g.eval r * r ^ 2) _ ((0 : ℝ) : ℂ) := h.add h2
    exact h3.congr_deriv (by simp)
  have h2 := (h1.comp_ofReal).const_mul A.det
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show (A + s • X).det = A.det * (1 + trace M * (s : ℂ) + g.eval (s : ℂ) * (s : ℂ) ^ 2)
  rw [h0, Matrix.det_one_add_smul]

theorem contDiff_det (k : WithTop ℕ∞) : ContDiff ℝ k (fun M : Matrix m m ℂ => M.det) := by
  simp_rw [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ (σ i) i)).contDiff

theorem fderiv_det_apply (A X : Matrix m m ℂ) (hA : IsUnit A.det) :
    fderiv ℝ (fun M : Matrix m m ℂ => M.det) A X = A.det * trace (A⁻¹ * X) := by
  have hd : DifferentiableAt ℝ (fun M : Matrix m m ℂ => M.det) A :=
    (contDiff_det 1).differentiable (by norm_num) A
  have hl : HasDerivAt (fun s : ℝ => A + s • X) X 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add A
    rwa [one_smul] at h
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h.unique (hasDerivAt_det_line A X hA)

theorem logDet_hess {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] Matrix m m ℂ)
    (hB : ∀ x, (B x x).IsHermitian) (t : E) (ht : 0 < (1 - B t t).det.re) :
    ContDiffAt ℝ 2 (fun x => Real.log (1 - B x x).det.re) t ∧
    ∀ u v, fderiv ℝ (fderiv ℝ (fun x => Real.log (1 - B x x).det.re)) t u v =
      -(trace ((1 - B t t)⁻¹ * (B t u + B u t) * (1 - B t t)⁻¹ * (B t v + B v t))).re
       - (trace ((1 - B t t)⁻¹ * (B u v + B v u))).re := by
  set Bc : E →L[ℝ] E →L[ℝ] Matrix m m ℂ := B.toContinuousBilinearMap with hBc
  have hBa : ∀ x y, Bc x y = B x y := fun _ _ => rfl
  let A : E → Matrix m m ℂ := fun x => 1 - B x x
  set Bf : E →L[ℝ] E →L[ℝ] Matrix m m ℂ := B.flip.toContinuousBilinearMap with hBf
  let D : E → E →L[ℝ] Matrix m m ℂ := fun x => -(Bc x + Bf x)
  have hDa : ∀ x v, D x v = -(B x v + B v x) := fun _ _ => rfl
  have hAd : ∀ x, HasFDerivAt A (D x) x := by
    intro x
    have h := Bc.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
    refine (h.const_sub 1).congr_fderiv ?_
    ext1 v
    rfl
  have hAc : ContDiff ℝ 2 A :=
    contDiff_const.sub (Bc.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id))
  let f : E → ℝ := fun x => (A x).det.re
  have hf : ContDiff ℝ 2 f := Complex.reCLM.contDiff.comp ((contDiff_det 2).comp hAc)
  have hcd : ContDiffAt ℝ 2 (fun x => Real.log (f x)) t := hf.contDiffAt.log ht.ne'
  have hreal : ∀ x, (A x).det = ((A x).det.re : ℂ) := by
    intro x
    have h1 : (A x)ᴴ = A x := by
      simp only [A, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (hB x).eq]
    have h2 := Matrix.det_conjTranspose (A x)
    rw [h1] at h2
    exact (Complex.conj_eq_iff_re.1 h2.symm).symm
  let T : Matrix m m ℂ →L[ℝ] ℝ :=
    Complex.reCLM ∘L LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℝ ℂ)
  have hTa : ∀ X, T X = (trace X).re := fun _ => rfl
  have hunit : ∀ x, 0 < f x → IsUnit (A x).det := by
    intro x hx
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    simp only [f, h0, Complex.zero_re, lt_self_iff_false] at hx
  have hFD : ∀ x, 0 < f x → ∀ v, fderiv ℝ (fun y => Real.log (f y)) x v = T ((A x)⁻¹ * D x v) := by
    intro x hx v
    have hdx := ((contDiff_det (m := m) 1).differentiable (by norm_num) (A x)).hasFDerivAt.comp x (hAd x)
    have hre := Complex.reCLM.hasFDerivAt.comp x hdx
    have hl := HasFDerivAt.log hre hx.ne'
    have hl' : HasFDerivAt (fun y => Real.log (f y)) _ x := hl
    rw [hl'.fderiv]
    show (f x)⁻¹ * (fderiv ℝ (fun M : Matrix m m ℂ => M.det) (A x) (D x v)).re = _
    rw [fderiv_det_apply _ _ (hunit x hx), hreal x, Complex.re_ofReal_mul]
    show (f x)⁻¹ * (f x * _) = _
    rw [inv_mul_cancel_left₀ hx.ne', hTa]
  refine ⟨hcd, fun u v => ?_⟩
  have hdiff : DifferentiableAt ℝ (fderiv ℝ fun x => Real.log (f x)) t :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e1 : fderiv ℝ (fderiv ℝ fun x => Real.log (f x)) t u v =
      fderiv ℝ (fun x => fderiv ℝ (fun y => Real.log (f y)) x v) t u := by
    have h := (hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const v t)).fderiv
    rw [h]; simp
  have hev : ∀ᶠ x in 𝓝 t, 0 < f x := (hf.continuous.tendsto t).eventually (lt_mem_nhds ht)
  have e2 : (fun x => fderiv ℝ (fun y => Real.log (f y)) x v) =ᶠ[𝓝 t] fun x => T ((A x)⁻¹ * D x v) :=
    hev.mono fun x hx => hFD x hx v
  obtain ⟨w, hw⟩ := (Matrix.isUnit_iff_isUnit_det _).2 (hunit t ht)
  have hwinv : (↑w⁻¹ : Matrix m m ℂ) = (A t)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hw, Ring.inverse_unit]
  have hI : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ (Matrix m m ℂ) ↑w⁻¹ ↑w⁻¹) (A t) := by
    rw [← hw]; exact hasFDerivAt_ringInverse w
  have hinv := hI.comp t (hAd t)
  have hfe : Ring.inverse ∘ A = fun x => (A x)⁻¹ := by
    funext x; exact (Matrix.nonsing_inv_eq_ringInverse _).symm
  rw [hfe] at hinv
  let Dv : E →L[ℝ] Matrix m m ℂ := -(Bf v + Bc v)
  have hDv : HasFDerivAt (fun x => D x v) Dv t := by
    have h : (fun x => D x v) = Dv := by funext x; rfl
    rw [h]; exact Dv.hasFDerivAt
  have hm := hinv.mul' hDv
  have hT := T.hasFDerivAt.comp t hm
  have hT' : HasFDerivAt (fun x => T ((A x)⁻¹ * D x v)) _ t := hT
  show fderiv ℝ (fderiv ℝ fun x => Real.log (f x)) t u v = _
  rw [e1, e2.fderiv_eq, hT'.fderiv]
  show T ((A t)⁻¹ * Dv u + (-((↑w⁻¹ : Matrix m m ℂ) * D t u * (↑w⁻¹ : Matrix m m ℂ))) * D t v) = _
  rw [hwinv, hTa]
  show (trace ((1 - B t t)⁻¹ * (-(B u v + B v u)) +
    (-((1 - B t t)⁻¹ * (-(B t u + B u t)) * (1 - B t t)⁻¹)) * (-(B t v + B v t)))).re = _
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.trace_add, Matrix.trace_neg, Complex.add_re,
    Complex.neg_re]
  ring

end Analysis

theorem trace_re_eq_conj {a : Type} [Fintype a] (X : Matrix a a ℂ) : (trace X).re = (trace Xᴴ).re := by
  rw [Matrix.trace_conjTranspose]; simp

theorem hP_eq {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (Z U V : Matrix a b ℂ) (Ai : Matrix b b ℂ) (Bi : Matrix a a ℂ) (hAi : Ai = (1 - Zᴴ * Z)⁻¹) (hA : Aiᴴ = Ai)
    (hB : Bi = 1 + Z * Ai * Zᴴ) :
    hP Z U V = 2 * (trace (Ai * Zᴴ * U * Ai * Zᴴ * V) + trace (Ai * Vᴴ * Bi * U)).re := by
  have ha : (trace (Ai * (Uᴴ * (Z * (Ai * (Vᴴ * Z)))))).re = (trace (Ai * (Zᴴ * (U * (Ai * (Zᴴ * V)))))).re := by
    rw [trace_re_eq_conj]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
    rw [show Zᴴ * (V * (Ai * (Zᴴ * (U * Ai)))) = (Zᴴ * V) * (Ai * (Zᴴ * (U * Ai))) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hb : (trace (Ai * (Uᴴ * (Z * (Ai * (Zᴴ * V)))))).re = (trace (Ai * (Zᴴ * (U * (Ai * (Vᴴ * Z)))))).re := by
    rw [trace_re_eq_conj]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
    rw [show Vᴴ * (Z * (Ai * (Zᴴ * (U * Ai)))) = (Vᴴ * Z) * (Ai * (Zᴴ * (U * Ai))) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have he : (trace (Ai * (Uᴴ * V))).re = (trace (Ai * (Vᴴ * U))).re := by
    rw [trace_re_eq_conj]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
    rw [show Vᴴ * (U * Ai) = (Vᴴ * U) * Ai by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  have hc : trace (Ai * (Vᴴ * (Z * (Ai * (Zᴴ * U))))) = trace (Ai * (Zᴴ * (U * (Ai * (Vᴴ * Z))))) := by
    rw [show Ai * (Vᴴ * (Z * (Ai * (Zᴴ * U)))) = (Ai * (Vᴴ * Z)) * (Ai * (Zᴴ * U)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  subst hB
  unfold hP
  rw [← hAi]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re, Matrix.mul_assoc, Matrix.mul_one,
    Matrix.one_mul, ha, hb, he, hc]
  ring

theorem inv_push {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (Z : Matrix a b ℂ) (h : IsUnit (1 - Zᴴ * Z).det) :
    (1 - Z * Zᴴ)⁻¹ = 1 + Z * (1 - Zᴴ * Z)⁻¹ * Zᴴ := by
  apply Matrix.inv_eq_right_inv
  have h1 := Matrix.mul_nonsing_inv _ h
  have h2 : Z * ((1 - Zᴴ * Z) * (1 - Zᴴ * Z)⁻¹) * Zᴴ = Z * Zᴴ := by rw [h1, Matrix.mul_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc] at h2 ⊢
  rw [← h2]
  abel

theorem levi_eq {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (Z U V : Matrix a b ℂ) (hZ : (1 - Zᴴ * Z).PosDef) :
    (((hP Z U V + hP Z (Complex.I • U) (Complex.I • V) : ℝ) : ℂ) +
      Complex.I * ((hP Z U (Complex.I • V) - hP Z (Complex.I • U) V : ℝ) : ℂ)) / 4 =
    trace ((1 - Zᴴ * Z)⁻¹ * Vᴴ * (1 - Z * Zᴴ)⁻¹ * U) := by
  have hu : IsUnit (1 - Zᴴ * Z).det := (Matrix.isUnit_iff_isUnit_det _).1 hZ.isUnit
  have hA : ((1 - Zᴴ * Z)⁻¹)ᴴ = (1 - Zᴴ * Z)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have e := fun U V => hP_eq Z U V _ _ rfl hA (inv_push Z hu)
  simp only [e]
  set Ai := (1 - Zᴴ * Z)⁻¹
  set Bi := (1 - Z * Zᴴ)⁻¹
  have s1 : ∀ c d : ℂ, trace (Ai * Zᴴ * (c • U) * Ai * Zᴴ * (d • V)) = c * d * trace (Ai * Zᴴ * U * Ai * Zᴴ * V) := by
    intro c d
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; ring
  have s2 : ∀ c d : ℂ, trace (Ai * (d • V)ᴴ * Bi * (c • U)) = c * star d * trace (Ai * Vᴴ * Bi * U) := by
    intro c d
    simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; ring
  have r1 := s1 1 Complex.I
  have r2 := s1 Complex.I 1
  have r3 := s1 Complex.I Complex.I
  have r4 := s2 1 Complex.I
  have r5 := s2 Complex.I 1
  have r6 := s2 Complex.I Complex.I
  simp only [one_smul, one_mul, mul_one, star_one] at r1 r2 r4 r5
  rw [r1, r2, r3, r4, r5, r6]
  set s := trace (Ai * Zᴴ * U * Ai * Zᴴ * V)
  set l := trace (Ai * Vᴴ * Bi * U)
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem det_blocks {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (P : Ψ → Matrix (Fin j) (Fin j) ℂ) (Q : Ψ → Matrix (Fin j') (Fin j') ℂ) :
    (Matrix.of fun x y : Fin n => if (q.symm x).1 = (q.symm y).1 then
      P (q.symm x).1 (q.symm y).2.1 (q.symm x).2.1 * Q (q.symm x).1 (q.symm x).2.2 (q.symm y).2.2 else 0).det =
    ∏ τ, (P τ).det ^ j' * (Q τ).det ^ j := by
  let r : Ψ × Fin j × Fin j' ≃ (Fin j × Fin j') × Ψ :=
    { toFun := fun x => ((x.2.1, x.2.2), x.1), invFun := fun x => (x.2, x.1.1, x.1.2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let e : Fin n ≃ (Fin j × Fin j') × Ψ := q.symm.trans r
  have h : (Matrix.of fun x y : Fin n => if (q.symm x).1 = (q.symm y).1 then
      P (q.symm x).1 (q.symm y).2.1 (q.symm x).2.1 * Q (q.symm x).1 (q.symm x).2.2 (q.symm y).2.2 else 0) =
      (Matrix.blockDiagonal fun τ => Matrix.kroneckerMap (· * ·) (P τ)ᵀ (Q τ)).submatrix e e := by
    ext x y
    simp only [Matrix.of_apply, Matrix.submatrix_apply, e, r, Equiv.trans_apply, Equiv.coe_fn_mk,
      Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Matrix.det_kronecker, Matrix.det_transpose]
  simp

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem ballMat_add (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Fin n → ℂ) (τ : Ψ) :
    ballMat q (u + v) τ = ballMat q u τ + ballMat q v τ := by ext; simp [ballMat]

theorem ballMat_smul (q : Ψ × Fin j × Fin j' ≃ Fin n) (c : ℂ) (u : Fin n → ℂ) (τ : Ψ) :
    ballMat q (c • u) τ = c • ballMat q u τ := by ext; simp [ballMat]

def ballB (q : Ψ × Fin j × Fin j' ≃ Fin n) (τ : Ψ) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] Matrix (Fin j') (Fin j') ℂ :=
  LinearMap.mk₂ ℝ (fun u v => (ballMat q u τ)ᴴ * ballMat q v τ)
    (fun u u' v => by simp [ballMat_add, Matrix.conjTranspose_add, Matrix.add_mul])
    (fun c u v => by
      have : ballMat q (c • u) τ = (c : ℂ) • ballMat q u τ := by ext; simp [ballMat]
      rw [this]; ext; simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_apply])
    (fun u v v' => by simp [ballMat_add, Matrix.mul_add])
    (fun c u v => by
      have : ballMat q (c • v) τ = (c : ℂ) • ballMat q v τ := by ext; simp [ballMat]
      rw [this]; ext; simp [Matrix.mul_smul, Matrix.smul_apply])

@[simp] theorem ballB_apply (q : Ψ × Fin j × Fin j' ≃ Fin n) (τ : Ψ) (u v : Fin n → ℂ) :
    ballB q τ u v = (ballMat q u τ)ᴴ * ballMat q v τ := rfl

theorem hess_sum {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ι → E → ℝ) (t : E)
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) t) (c : ℝ) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun x => c * ∑ i, f i x)) t u v = c * ∑ i, fderiv ℝ (fderiv ℝ (f i)) t u v := by
  have h1 : ∀ i, ∀ᶠ x in 𝓝 t, DifferentiableAt ℝ (f i) x := fun i =>
    ((hf i).eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have h2 : ∀ i, DifferentiableAt ℝ (fderiv ℝ (f i)) t := fun i =>
    ((hf i).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h3 : fderiv ℝ (fun x => c * ∑ i, f i x) =ᶠ[𝓝 t] fun x => c • ∑ i, fderiv ℝ (f i) x := by
    filter_upwards [eventually_all.2 h1] with x hx
    have : HasFDerivAt (fun x => c * ∑ i, f i x) (c • ∑ i, fderiv ℝ (f i) x) x :=
      (HasFDerivAt.fun_sum fun i _ => (hx i).hasFDerivAt).const_mul c
    exact this.fderiv
  rw [h3.fderiv_eq]
  have h4 : HasFDerivAt (fun x => c • ∑ i, fderiv ℝ (f i) x) (c • ∑ i, fderiv ℝ (fderiv ℝ (f i)) t) t :=
    (HasFDerivAt.fun_sum fun i _ => (h2 i).hasFDerivAt).const_smul c
  rw [h4.fderiv]
  simp [ContinuousLinearMap.sum_apply]

theorem det_pos_of_posDef {m : Type} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ} (h : A.PosDef) :
    0 < A.det.re ∧ A.det = (A.det.re : ℂ) := by
  have := h.det_pos
  have h2 := Complex.pos_iff.1 this
  exact ⟨h2.1, Complex.ext (by simp) (by simpa using h2.2.symm)⟩

theorem ballMat_single (q : Ψ × Fin j × Fin j' ≃ Fin n) [DecidableEq Ψ] (x : Fin n) (τ : Ψ) :
    ballMat q (Pi.single x 1) τ = if (q.symm x).1 = τ then Matrix.single (q.symm x).2.1 (q.symm x).2.2 1 else 0 := by
  ext a b
  have e : q (τ, a, b) = x ↔ (τ, a, b) = q.symm x := by
    rw [Equiv.eq_symm_apply]
  by_cases h : (q.symm x).1 = τ
  · simp only [h, if_true, ballMat, Matrix.of_apply, Pi.single_apply, e]
    simp only [Matrix.single_apply, Prod.ext_iff, h, true_and]
    by_cases h1 : a = (q.symm x).2.1 <;> by_cases h2 : b = (q.symm x).2.2 <;> simp [h1, h2, eq_comm]
  · simp only [h, if_false, ballMat, Matrix.of_apply, Pi.single_apply, e, Matrix.zero_apply]
    rw [if_neg]
    intro h'
    exact h (by rw [← h'])

theorem trace_single {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (X : Matrix b b ℂ) (Y : Matrix a a ℂ) (a1 a2 : a) (b1 b2 : b) :
    trace (X * (Matrix.single a2 b2 (1 : ℂ))ᴴ * Y * Matrix.single a1 b1 (1 : ℂ)) = X b1 b2 * Y a2 a1 := by
  rw [Matrix.conjTranspose_single, star_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem hess_ball (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (ht : t ∈ ballDom q) (u v : Fin n → ℂ) :
    fderiv ℝ (fderiv ℝ (fun t' => ballPot q t' / 2)) t u v =
      (1 / 2 : ℝ) * ∑ τ, hP (ballMat q t τ) (ballMat q u τ) (ballMat q v τ) := by
  have hdp := fun τ => (det_pos_of_posDef (ht τ)).1
  have hH := fun τ => logDet_hess (ballB q τ) (fun x => by
    show ((ballMat q x τ)ᴴ * ballMat q x τ).IsHermitian
    exact Matrix.isHermitian_conjTranspose_mul_self _) t (hdp τ)
  have e : (fun t' => ballPot q t' / 2) =
      fun t' => (-1 / 2 : ℝ) * ∑ τ, (fun x => Real.log (1 - ballB q τ x x).det.re) t' := by
    funext t'; simp only [ballPot, ballB_apply]; ring
  rw [e, hess_sum _ t (fun τ => (hH τ).1)]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [(hH τ).2 u v]
  simp only [hP, ballB_apply]
  ring

theorem comb_sum (a b c d : Ψ → ℝ) :
    ((((1 / 2 : ℝ) * ∑ τ, a τ + (1 / 2 : ℝ) * ∑ τ, b τ : ℝ) : ℂ) +
      Complex.I * (((1 / 2 : ℝ) * ∑ τ, c τ - (1 / 2 : ℝ) * ∑ τ, d τ : ℝ) : ℂ)) / 4 =
    (1 / 2 : ℂ) * ∑ τ, (((a τ + b τ : ℝ) : ℂ) + Complex.I * ((c τ - d τ : ℝ) : ℂ)) / 4 := by
  push_cast
  simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem cxHessian_ball [DecidableEq Ψ] (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (ht : t ∈ ballDom q) :
    cxHessian (fun t' => ballPot q t' / 2) t = (1 / 2 : ℂ) • Matrix.of fun x y : Fin n =>
      if (q.symm x).1 = (q.symm y).1 then
      ((1 - ballMat q t (q.symm x).1 * (ballMat q t (q.symm x).1)ᴴ)⁻¹ : Matrix (Fin j) (Fin j) ℂ) (q.symm y).2.1 (q.symm x).2.1 *
       ((1 - (ballMat q t (q.symm x).1)ᴴ * ballMat q t (q.symm x).1)⁻¹ : Matrix (Fin j') (Fin j') ℂ) (q.symm x).2.2 (q.symm y).2.2 else 0 := by
  ext x y
  simp only [cxHessian, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, hess_ball q t ht, ballMat_smul]
  have key := fun τ => levi_eq (ballMat q t τ) (ballMat q (Pi.single x 1) τ) (ballMat q (Pi.single y 1) τ) (ht τ)
  have e2 : ∑ τ, trace ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹ * (ballMat q (Pi.single y 1) τ)ᴴ *
      (1 - ballMat q t τ * (ballMat q t τ)ᴴ)⁻¹ * ballMat q (Pi.single x 1) τ) =
      if (q.symm x).1 = (q.symm y).1 then
      ((1 - ballMat q t (q.symm x).1 * (ballMat q t (q.symm x).1)ᴴ)⁻¹ : Matrix (Fin j) (Fin j) ℂ) (q.symm y).2.1 (q.symm x).2.1 *
       ((1 - (ballMat q t (q.symm x).1)ᴴ * ballMat q t (q.symm x).1)⁻¹ : Matrix (Fin j') (Fin j') ℂ) (q.symm x).2.2 (q.symm y).2.2 else 0 := by
    rw [Finset.sum_eq_single (q.symm x).1]
    · rw [ballMat_single q x, if_pos rfl, ballMat_single q y]
      by_cases h : (q.symm x).1 = (q.symm y).1
      · rw [if_pos h.symm, if_pos h, trace_single, mul_comm]
      · rw [if_neg (Ne.symm h), if_neg h]; simp
    · intro τ _ hτ
      rw [ballMat_single q x, if_neg (Ne.symm hτ)]; simp
    · simp
  rw [← e2, ← Finset.sum_congr rfl fun τ _ => key τ]
  exact comb_sum _ _ _ _

theorem maDensity_half_ballPot (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ ballDom q, maDensity (fun (_ : Fin n) t' => ballPot q t' / 2) t = c * ballDens q t := by
  classical
  refine ⟨(n.factorial : ℝ) * (2 / Real.pi) ^ n * (1 / 2) ^ n, by positivity, fun t ht => ?_⟩
  have hd := fun τ => det_pos_of_posDef (ht τ)
  have hdet : ∀ τ, (1 - ballMat q t τ * (ballMat q t τ)ᴴ).det = (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det :=
    fun τ => Matrix.det_one_sub_mul_comm _ _
  have hD : (cxHessian (fun t' => ballPot q t' / 2) t).det =
      (((1 / 2) ^ n * ballDens q t : ℝ) : ℂ) := by
    rw [cxHessian_ball q t ht, Matrix.det_smul, Fintype.card_fin]
    have := det_blocks q (fun τ => (1 - ballMat q t τ * (ballMat q t τ)ᴴ)⁻¹)
      (fun τ => (1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹)
    rw [this]
    have hb : ballDens q t = ∏ τ, ((1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re)⁻¹ ^ (j + j') := by
      simp only [ballDens, ballPot, mul_neg, ← Finset.sum_neg_distrib, Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [← mul_neg, ← Real.log_inv, mul_comm, Real.exp_mul, Real.exp_log (inv_pos.2 (hd τ).1), Real.rpow_natCast]
    rw [hb]
    push_cast
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_nonsing_inv, Matrix.det_nonsing_inv, hdet τ, Ring.inverse_eq_inv', (hd τ).2]
    simp only [Complex.ofReal_re]
    rw [pow_add, mul_comm]
  simp only [maDensity, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mixedDiscriminant_constant, hD, Complex.ofReal_re]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.BallHess
