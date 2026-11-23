import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.SmoothMajorants.Bounds

noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3.K Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.LCDer

def mulTwoByThree : M23 →ₗ[ℝ] complexMatrix3 →ₗ[ℝ] M23 :=
  LinearMap.mk₂ ℝ (fun X M => Matrix.of.symm (Matrix.of X * Matrix.of M))
    (fun X Y M => by ext r c; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc])
    (fun X M N => by ext r c; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm])

def mulB : M23 →L[ℝ] complexMatrix3 →L[ℝ] M23 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (complexMatrix3 →ₗ[ℝ] M23) ≃ₗ[ℝ] (complexMatrix3 →L[ℝ] M23)).toLinearMap ∘ₗ mulTwoByThree)

theorem mulB_apply (X : M23) (M : complexMatrix3) : mulB X M = Matrix.of.symm (Matrix.of X * Matrix.of M) := rfl

def mulThreeByThree : complexMatrix3 →ₗ[ℝ] complexMatrix3 →ₗ[ℝ] complexMatrix3 :=
  LinearMap.mk₂ ℝ (fun X M => Matrix.of.symm (Matrix.of X * Matrix.of M))
    (fun X Y M => by ext r c; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc])
    (fun X M N => by ext r c; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib])
    (fun a X M => by ext r c; simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm])

def mul3 : complexMatrix3 →L[ℝ] complexMatrix3 →L[ℝ] complexMatrix3 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (complexMatrix3 →ₗ[ℝ] complexMatrix3) ≃ₗ[ℝ] (complexMatrix3 →L[ℝ] complexMatrix3)).toLinearMap ∘ₗ mulThreeByThree)

def Rm (M : complexMatrix3) : M23 →L[ℝ] M23 := mulB.flip M

theorem Rm_apply (M : complexMatrix3) (X : M23) : Rm M X = Matrix.of.symm (Matrix.of X * Matrix.of M) := rfl

def Rq (M : complexMatrix3) : E5 →L[ℝ] E5 := (Rm M).prodMap (ContinuousLinearMap.id ℝ (Fin 2 → ℂ))

theorem Rq_apply (M : complexMatrix3) (X : E5) : Rq M X = (Rm M X.1, X.2) := rfl

def minv (M : complexMatrix3) : complexMatrix3 := Matrix.of.symm (Matrix.of M)⁻¹

def nb (M : complexMatrix3) : Set complexMatrix3 :=
  {M' | (Matrix.of M').det ≠ 0 ∧ ‖minv M'‖ < ‖minv M‖ + 1 ∧ ‖M'‖ < ‖M‖ + 1}

def ell (M : complexMatrix3) (i j : Fin 3) : complexMatrix3 →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) j).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℂ) i).comp (mul3 (minv M)))

def ellc (M : complexMatrix3) (i j : Fin 3) : complexMatrix3 →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp (ell M i j)

theorem ell_apply (M : complexMatrix3) (i j : Fin 3) (m : complexMatrix3) :
    ell M i j m = ((Matrix.of M)⁻¹ * Matrix.of m) i j := rfl

theorem ellc_apply (M : complexMatrix3) (i j : Fin 3) (m : complexMatrix3) :
    ellc M i j m = (starRingEnd ℂ) (((Matrix.of M)⁻¹ * Matrix.of m) i j) := rfl

def J (Q : Sw) (M : complexMatrix3) (h : M22) (t : ℂ) : ℂ := innB (fun X => Q (Rq M X)) h t 1 1

def wt (k : ℕ) (p : M22 × ℂ) : ℂ :=
  ph (4 * (k : ℤ) - 4) p.2 * ph (-(2 * (k : ℤ) - 2)) (Matrix.of p.1).det *
    ((‖(Matrix.of p.1).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)

def G (k : ℕ) (Q : Sw) (M : complexMatrix3) (p : M22 × ℂ) : ℂ := J Q M p.1 p.2 * wt k p

def dInn (Q : Sw) (h : M22) (t : ℂ) (M : complexMatrix3) : complexMatrix3 →L[ℝ] ℂ :=
  ∑ i, ∑ j, ((J (PH i j Q) M h t - if i = j then J Q M h t else 0) • ell M i j +
    (J (PA i j Q) M h t - if i = j then J Q M h t else 0) • ellc M i j)

theorem Rm_minv {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) (X : M23) : Rm (minv M) (Rm M X) = X := by
  have hu : IsUnit (Matrix.of M).det := isUnit_iff_ne_zero.mpr hM
  simp only [Rm_apply, minv, Equiv.apply_symm_apply, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rfl

theorem norm_Rm_le (M : complexMatrix3) : ‖Rm M‖ ≤ ‖mulB‖ * ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun X => ?_
  calc ‖Rm M X‖ = ‖mulB X M‖ := rfl
    _ ≤ ‖mulB X‖ * ‖M‖ := (mulB X).le_opNorm M
    _ ≤ ‖mulB‖ * ‖X‖ * ‖M‖ := by gcongr; exact mulB.le_opNorm X
    _ = ‖mulB‖ * ‖M‖ * ‖X‖ := by ring

theorem norm_ell_le (M : complexMatrix3) (i j : Fin 3) : ‖ell M i j‖ ≤ ‖mul3‖ * ‖minv M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun m => ?_
  have h1 : ‖ell M i j m‖ = ‖mul3 (minv M) m i j‖ := rfl
  rw [h1]
  calc ‖mul3 (minv M) m i j‖ ≤ ‖mul3 (minv M) m i‖ := norm_le_pi_norm _ j
    _ ≤ ‖mul3 (minv M) m‖ := norm_le_pi_norm _ i
    _ ≤ ‖mul3 (minv M)‖ * ‖m‖ := (mul3 (minv M)).le_opNorm m
    _ ≤ ‖mul3‖ * ‖minv M‖ * ‖m‖ := by gcongr; exact mul3.le_opNorm _

theorem norm_ellc_le (M : complexMatrix3) (i j : Fin 3) : ‖ellc M i j‖ ≤ ‖mul3‖ * ‖minv M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun m => ?_
  have h1 : ‖ellc M i j m‖ = ‖ell M i j m‖ := by
    rw [ellc_apply, ell_apply, RCLike.norm_conj]
  rw [h1]
  exact ((ell M i j).le_opNorm m).trans (by gcongr; exact norm_ell_le M i j)

theorem nb_mem {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) : nb M ∈ 𝓝 M := by
  have hdet : Continuous (fun M' : complexMatrix3 => (Matrix.of M').det) :=
    Continuous.matrix_det (by exact continuous_id)
  have hinv : ContinuousAt minv M := by
    have := continuousAt_matrix_inv (Matrix.of M) (by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hM)
    exact this
  have h1 : ∀ᶠ M' in 𝓝 M, (Matrix.of M').det ≠ 0 := hdet.continuousAt.eventually_ne hM
  have h2 : ∀ᶠ M' in 𝓝 M, ‖minv M'‖ < ‖minv M‖ + 1 :=
    (continuous_norm.continuousAt.comp hinv).eventually (gt_mem_nhds (lt_add_one _))
  have h3 : ∀ᶠ M' in 𝓝 M, ‖M'‖ < ‖M‖ + 1 :=
    continuous_norm.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [h1, h2, h3] with M' a b c using ⟨a, b, c⟩

theorem self_mem_nb {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) : M ∈ nb M :=
  ⟨hM, lt_add_one _, lt_add_one _⟩

theorem nb_det {M M' : complexMatrix3} (h : M' ∈ nb M) : (Matrix.of M').det ≠ 0 := h.1

theorem nb_inv {M M' : complexMatrix3} (h : M' ∈ nb M) : ‖Rm (minv M')‖ ≤ ‖mulB‖ * (‖minv M‖ + 1) :=
  (norm_Rm_le _).trans (by gcongr; exact h.2.1.le)

theorem nb_fwd {M M' : complexMatrix3} (h : M' ∈ nb M) : ‖Rm M'‖ ≤ ‖mulB‖ * (‖M‖ + 1) :=
  (norm_Rm_le _).trans (by gcongr; exact h.2.2.le)

theorem nb_ell {M M' : complexMatrix3} (h : M' ∈ nb M) (i j : Fin 3) : ‖ell M' i j‖ ≤ ‖mul3‖ * (‖minv M‖ + 1) :=
  (norm_ell_le _ _ _).trans (by gcongr; exact h.2.1.le)

theorem nb_ellc {M M' : complexMatrix3} (h : M' ∈ nb M) (i j : Fin 3) : ‖ellc M' i j‖ ≤ ‖mul3‖ * (‖minv M‖ + 1) :=
  (norm_ellc_le _ _ _).trans (by gcongr; exact h.2.1.le)

def gl (M : complexMatrix3) (hM : (Matrix.of M).det ≠ 0) : GL (Fin 3) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of M) hM

theorem gl_val (M : complexMatrix3) (hM : (Matrix.of M).det ≠ 0) :
    ((gl M hM : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.of M := rfl

theorem inn_eq_J (Q : Sw) (M : complexMatrix3) (hM : (Matrix.of M).det ≠ 0) (h : M22) (t : ℂ) :
    inn Q (gl M hM) (Matrix.of h) t = J Q M h t := by
  simp only [inn, J, innB, Rq_apply, Rm_apply, gl_val, one_mul, Equiv.apply_symm_apply]

theorem secI_eq_G (k : ℕ) (Q : Sw) (M : complexMatrix3) (hM : (Matrix.of M).det ≠ 0) (p : M22 × ℂ) :
    secI k Q (gl M hM) p = G k Q M p := by
  simp only [secI, G, wt, inn_eq_J, mul_assoc]

end GlobalTheory.CompanionTheory.LCDer
