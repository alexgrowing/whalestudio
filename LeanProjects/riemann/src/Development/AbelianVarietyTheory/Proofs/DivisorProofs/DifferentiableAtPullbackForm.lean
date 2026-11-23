import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.PullCoefDiff

theorem repr_mul_eq_sum {n : ℕ} (x y : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (x * y) S =
      ∑ A, ∑ B, (bas n).repr x A * (bas n).repr y B * (bas n).repr (bas n A * bas n B) S := by
  conv_lhs => rw [← (bas n).sum_repr x, ← (bas n).sum_repr y]
  rw [Finset.sum_mul_sum]
  simp only [map_sum, Finsupp.finset_sum_apply, smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem ι_eq_sum {m : ℕ} (u : Fin m ⊕ Fin m → ℂ) :
    ExteriorAlgebra.ι ℂ u = ∑ a, u (.inl a) • dz a + ∑ a, u (.inr a) • dzb a := by
  simp only [dz, dzb, ← map_smul, ← map_sum, ← map_add]
  refine congrArg _ (funext ?_)
  rintro (b | b) <;> simp [Pi.single_apply, Finset.sum_apply]

theorem differentiableAt_repr_pull {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : E → V n →L[ℂ] V m} {v : E} (hL : ∀ b a, DifferentiableAt ℝ (fun x => L x (coordVec b) a) v)
    (θ : Alt m) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun x => (bas n).repr (pull (L x) θ) S) v := by
  induction θ using ExteriorAlgebra.induction generalizing S with
  | algebraMap r => simp only [AlgHom.commutes]; exact differentiableAt_const _
  | ι u =>
    rw [ι_eq_sum]
    simp only [map_add, map_sum, map_smul, (pull_dz _ _).1, (pull_dz _ _).2, Finsupp.add_apply,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    refine DifferentiableAt.add ?_ ?_
    · exact DifferentiableAt.fun_sum fun a _ => (DifferentiableAt.fun_sum fun b _ => (hL b a).mul_const _).const_mul _
    · refine DifferentiableAt.fun_sum fun a _ => (DifferentiableAt.fun_sum fun b _ =>
        DifferentiableAt.mul_const ?_ _).const_mul _
      exact Complex.conjCLE.differentiableAt.comp v (hL b a)
  | mul a b ha hb =>
    simp only [map_mul, repr_mul_eq_sum (pull _ a)]
    exact DifferentiableAt.fun_sum fun A _ => DifferentiableAt.fun_sum fun B _ => ((ha A).mul (hb B)).mul_const _
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply]
    exact (ha S).add (hb S)

theorem differentiableAt_repr_pull_fderiv : ∀ {n m : ℕ} {φ : V n → V m} {U : Set (V n)}, IsOpen U →
    DifferentiableOn ℂ φ U → ∀ {v : V n}, v ∈ U → ∀ (θ : Alt m) (S : Finset (Fin (n + n))),
    DifferentiableAt ℝ (fun x => (bas n).repr (pull (fderiv ℂ φ x) θ) S) v := by
  intro n m φ U hU hφ v hv θ S
  refine differentiableAt_repr_pull (fun b a => ?_) θ S
  have h₁ : ContDiffAt ℂ 2 φ v := GlobalTheory.SCV.contDiffAt_of_differentiableOn hφ (hU.mem_nhds hv) 2
  have h₂ : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h₃ : DifferentiableAt ℂ (fun x => fderiv ℂ φ x (coordVec b)) v := h₂.clm_apply (differentiableAt_const _)
  have h₄ : DifferentiableAt ℂ (fun x => fderiv ℂ φ x (coordVec b) a) v :=
    (EuclideanSpace.proj (𝕜 := ℂ) a).differentiableAt.comp v h₃
  exact h₄.restrictScalars ℝ

end GlobalTheory.PullCoefDiff
