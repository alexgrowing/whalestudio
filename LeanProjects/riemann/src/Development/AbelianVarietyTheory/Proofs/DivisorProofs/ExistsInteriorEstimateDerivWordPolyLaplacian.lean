import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantVectorFieldsExpCoordsSmoothFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticWeakSolWordDerivLeConstMulSupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticWeakSolOfPolynomialLaplacianZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivWordExpCoordsDifferentialOperatorStatement
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold

namespace GlobalTheory

open ZetaZeros.D.EllReg GlobalTheory.HCA

theorem foldr_rightDeriv_leftTranslate {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    (F : G → ℂ) (g : G) (l : List 𝔤) :
    l.foldr h.rightDeriv (fun y => F (g * y)) = fun y => l.foldr h.rightDeriv F (g * y) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    funext y
    simp only [IsExpLieAlgebra.rightDeriv, mul_assoc]

theorem interior_word_bound : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ Kc : Set G, IsCompact Kc ∧ ∀ l : List 𝔤, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ (g : G) (M : ℝ), (∀ y ∈ Kc, ‖(f : G → ℂ) (g * y)‖ ≤ M) → ‖l.foldr h.rightDeriv (f : G → ℂ) g‖ ≤ C * M := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP
  obtain ⟨r₁, hr₁, m, a, ha, hell, hsol⟩ := GlobalTheory.T.exists_elliptic_weakSol_of_polynomial_laplacian_zero 𝔸 G 𝔤 h d b P hP
  obtain ⟨r₂, hr₂, c, hc⟩ := GlobalTheory.T.leftInvariantVectorFields_expCoords_smooth_frame 𝔸 G 𝔤 h d b
  refine ⟨(fun x : E d => h.expG (coordEquiv b x)) '' Metric.closedBall 0 r₁,
    (isCompact_closedBall 0 r₁).image (h.continuous_expG.comp (coordEquiv b).continuous), ?_⟩
  intro l
  obtain ⟨al, -, hword⟩ := GlobalTheory.T.rightDerivWord_expCoords_differentialOperator 𝔸 G 𝔤 h d b r₂ c hc l
  have hsup : ∀ w : List (Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u (Metric.ball 0 r₁) →
      WeakSol (oneSys m a) (Metric.ball 0 r₁) u → ∀ M : ℝ, (∀ x ∈ Metric.ball (0 : E d) r₁, ‖u x‖ ≤ M) →
      ‖dw w u 0‖ ≤ C * M := fun w =>
    GlobalTheory.T.elliptic_weakSol_wordDeriv_le_const_mul_sup d Unit (oneSys m a) (Metric.ball 0 r₁) Metric.isOpen_ball (fun _ n w => ha n w)
      (fun x hx ξ hξ => ⟨(), hell x hx ξ hξ⟩) w 0 (Metric.mem_ball_self hr₁)
  choose Cw hCw0 hCw using hsup
  refine ⟨∑ n ∈ Finset.range (l.length + 1), ∑ w : Fin n → Fin d, ‖al n w 0‖ * Cw (List.ofFn w),
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun w _ => mul_nonneg (norm_nonneg _) (hCw0 _), ?_⟩
  intro f hf g M hM
  have hfs : h.IsSmoothFun (f : G → ℂ) := f.2
  have hf' : h.IsSmoothFun (fun y : G => (f : G → ℂ) (g * y)) := by
    letI := h.chartedSpace
    haveI := h.lieGroup ∞
    exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hfs (contMDiff_const.mul contMDiff_id)
  have key : l.foldr h.rightDeriv (f : G → ℂ) g =
      apOp l.length al (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) 0 := by
    have := hword _ hf' 0 (Metric.mem_ball_self hr₂)
    rw [foldr_rightDeriv_leftTranslate] at this
    simpa [coordEquiv_zero] using this
  have hu : ContinuousOn (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) (Metric.ball 0 r₁) :=
    (h.contDiff_comp_coordEquiv hfs g b).continuous.continuousOn
  have hbd : ∀ x ∈ Metric.ball (0 : E d) r₁, ‖(f : G → ℂ) (g * h.expG (coordEquiv b x))‖ ≤ M :=
    fun x hx => hM _ ⟨x, Metric.ball_subset_closedBall hx, rfl⟩
  have hdw : ∀ w : List (Fin d),
      ‖dw w (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) 0‖ ≤ Cw w * M :=
    fun w => hCw w _ hu (hsol f hf g) M hbd
  rw [key, apOp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdw _) (norm_nonneg _)

end GlobalTheory
