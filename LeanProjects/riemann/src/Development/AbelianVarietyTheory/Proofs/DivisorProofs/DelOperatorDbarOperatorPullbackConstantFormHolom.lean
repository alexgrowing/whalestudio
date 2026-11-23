import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.PullDelClosed

open GlobalTheory.CxForm.FormMul GlobalTheory.CxForm.PullClosed

variable {n m : ℕ}

theorem delAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {f : ι → V n → ℂ} (e : ι → Alt n)
    (hf : ∀ i, DifferentiableAt ℝ (f i) v) :
    delAt (fun x => ∑ i, f i x • e i) v = ∑ a, ∑ i, del (f i) v (coordVec a) • (dz a * e i) := by
  unfold delAt
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : coefwise (fun g => del g v (coordVec a)) (fun x => ∑ i, f i x • e i) =
      ∑ i, del (f i) v (coordVec a) • e i := by
    refine (bas n).ext_elem fun S => ?_
    rw [repr_coefwise, repr_sum_smul,
      del_sum (A := fun i x => f i x * (bas n).repr (e i) S) fun i _ => (hf i).mul (differentiableAt_const _),
      ContinuousLinearMap.sum_apply, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_mul (b := fun _ => (bas n).repr (e i) S) (hf i) (differentiableAt_const _), del_const]
    simp
  rw [h, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem delAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  unfold delAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_add]
  congr 1
  refine (bas n).ext_elem fun S => ?_
  rw [map_add, Finsupp.add_apply, repr_coefwise, repr_coefwise, repr_coefwise, ← ContinuousLinearMap.add_apply,
    ← del_add (hF S) (hG S)]
  simp only [map_add, Finsupp.add_apply]

theorem sum_symm_dz {s : Fin n → Fin n → ℂ} (hs : ∀ a c, s a c = s c a) :
    ∑ a, ∑ c, s a c • (dz a * dz c : Alt n) = 0 := by
  have h := congrArg swap (sum_symm_dzb hs)
  simpa only [map_sum, map_smul, map_mul, map_zero, fun a : Fin n => (swap_dz a).2] using h

theorem delAt_pull_of_contDiffAt {φ : V n → V m} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) (θ : Alt m) :
    delAt (fun x => pull (fderiv ℂ φ x) θ) v = 0 := by
  have hD : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hJ (w : V n) (b : Fin m) : HasFDerivAt (fun x => fderiv ℂ φ x w b)
      (((EuclideanSpace.proj b : V m →L[ℂ] ℂ).comp (ContinuousLinearMap.apply ℂ (V m) w)).comp
        (fderiv ℂ (fderiv ℂ φ) v)) v :=
    ((EuclideanSpace.proj b : V m →L[ℂ] ℂ).comp (ContinuousLinearMap.apply ℂ (V m) w)).hasFDerivAt.comp v
      hD.hasFDerivAt
  have hJR (w : V n) (b : Fin m) : DifferentiableAt ℝ (fun x => fderiv ℂ φ x w b) v :=
    (hJ w b).differentiableAt.restrictScalars ℝ
  have hJc (w : V n) (b : Fin m) : DifferentiableAt ℝ (fun x => conj (fderiv ℂ φ x w b)) v :=
    Complex.conjCLE.differentiableAt.comp v (hJR w b)
  have hs := hφ.isSymmSndFDerivAt (by simp)
  have hd (θ : Alt m) := (diff_and_closed hφ θ).1
  set P : Alt m → Prop := fun θ => delAt (fun x => pull (fderiv ℂ φ x) θ) v = 0 with hP
  have hconst (r : ℂ) : P (algebraMap ℂ _ r) := by
    simp only [hP, AlgHom.commutes]
    simp [delAt, coefwise]
  have hadd (a b : Alt m) (ha : P a) (hb : P b) : P (a + b) := by
    simp only [hP, map_add] at ha hb ⊢
    rw [delAt_add (hd a) (hd b), ha, hb, add_zero]
  have hmul (a b : Alt m) (ha : P a) (hb : P b) : P (a * b) := by
    simp only [hP, map_mul] at ha hb ⊢
    obtain ⟨y, hy⟩ := delAt_mul (hd a) (hd b)
    rw [hy, ha, hb, zero_mul, mul_zero, add_zero]
  have hgen (i : Fin m ⊕ Fin m) : P (ExteriorAlgebra.ι ℂ (Pi.single i 1)) := by
    rcases i with b | b
    · change P (dz b)
      simp only [hP, fun L : V n →L[ℂ] V m => (pull_dz L b).1]
      rw [delAt_sum_smul _ fun c => hJR _ b]
      refine sum_symm_dz fun a c => ?_
      rw [del_eq_fderiv (hJ _ b).differentiableAt, del_eq_fderiv (hJ _ b).differentiableAt,
        (hJ _ b).fderiv, (hJ _ b).fderiv]
      simp [hs.eq (coordVec a) (coordVec c)]
    · change P (dzb b)
      simp only [hP, fun L : V n →L[ℂ] V m => (pull_dz L b).2]
      rw [delAt_sum_smul _ fun c => hJc _ b]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
      rw [del_conj, dbar_eq_zero (hJ _ b).differentiableAt]
      simp
  change P θ
  induction θ using ExteriorAlgebra.induction with
  | algebraMap r => exact hconst r
  | ι u =>
    rw [pi_eq_sum_univ' u, map_sum]
    refine Finset.sum_induction _ P hadd (by simpa using hconst 0) fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    exact hmul _ _ (hconst _) (hgen i)
  | mul a b ha hb => exact hmul a b ha hb
  | add a b ha hb => exact hadd a b ha hb

theorem delAt_dbarAt_pull_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U →
    DifferentiableOn ℂ τ U →
    ∀ v ∈ U, delAt (fun x => pull (fderiv ℂ τ x) γ) v = 0 ∧ dbarAt (fun x => pull (fderiv ℂ τ x) γ) v = 0 :=
  fun _ _ _ _ γ hU hτ _ hv =>
    ⟨delAt_pull_of_contDiffAt (analyticOnNhd_of_holo hU hτ _ hv).contDiffAt γ, dbarAt_pull_fderiv hU hτ hv γ⟩

end GlobalTheory.CxForm.PullDelClosed
