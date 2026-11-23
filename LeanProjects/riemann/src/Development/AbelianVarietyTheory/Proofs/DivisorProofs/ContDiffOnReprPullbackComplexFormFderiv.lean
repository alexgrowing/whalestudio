import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.PullSmooth

theorem repr_mul {m : ℕ} (a b : Alt m) (S : Finset (Fin (m + m))) :
    (bas m).repr (a * b) S = ∑ S₁, ∑ S₂, (bas m).repr a S₁ * (bas m).repr b S₂ *
      (bas m).repr (bas m S₁ * bas m S₂) S := by
  conv_lhs => rw [← (bas m).sum_repr a, ← (bas m).sum_repr b]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

theorem entries_smooth {m n : ℕ} {τ : V m → V n} {U : Set (V m)} (hU : IsOpen U) (hτ : DifferentiableOn ℂ τ U)
    (v : V m) (a : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U ∧ ContDiffOn ℝ ∞ (fun x => conj (fderiv ℂ τ x v a)) U := by
  have h₁ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x) U :=
    ContDiffOn.fderiv_of_isOpen (n := ω) (m := ∞)
      (((GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn hU).2 hτ).contDiffOn hU.uniqueDiffOn) hU le_top
  have h₂ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x v a) U :=
    (EuclideanSpace.proj a : V n →L[ℂ] ℂ).contDiff.comp_contDiffOn (h₁.clm_apply contDiffOn_const)
  have h₃ : ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U := h₂.restrict_scalars ℝ
  exact ⟨h₃, Complex.conjCLE.contDiff.comp_contDiffOn h₃⟩

theorem contDiffOn_repr_pull_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U →
    DifferentiableOn ℂ τ U → ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  intro m n τ U γ hU hτ
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r =>
    intro S
    simp only [AlgHom.commutes]
    exact contDiffOn_const
  | ι u =>
    intro S
    have hcoef : ∀ x, (bas m).repr (pull (fderiv ℂ τ x) (ExteriorAlgebra.ι ℂ u)) S =
        ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)
          (Matrix.toLin' (Matrix.fromBlocks (Matrix.of fun b a => fderiv ℂ τ x (coordVec b) a) 0 0
            (Matrix.of fun b a => conj (fderiv ℂ τ x (coordVec b) a))) u) := by
      intro x
      simp [pull, ExteriorAlgebra.map_apply_ι]
    simp_rw [hcoef]
    refine (LinearMap.toContinuousLinearMap ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)).contDiff.restrict_scalars ℝ
      |>.comp_contDiffOn ?_
    refine contDiffOn_pi.2 fun i => ?_
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ contDiffOn_const
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).1
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).2
  | mul a b ha hb =>
    intro S
    have e : (fun x => (bas m).repr (pull (fderiv ℂ τ x) (a * b)) S) = fun x => ∑ S₁, ∑ S₂,
        (bas m).repr (pull (fderiv ℂ τ x) a) S₁ * (bas m).repr (pull (fderiv ℂ τ x) b) S₂ *
          (bas m).repr (bas m S₁ * bas m S₂) S := funext fun x => by rw [map_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun S₁ _ => ContDiffOn.sum fun S₂ _ =>
      ((ha S₁).mul (hb S₂)).mul contDiffOn_const
  | add a b ha hb =>
    intro S
    simp only [map_add, Finsupp.add_apply]
    exact (ha S).add (hb S)

end GlobalTheory.PullSmooth
