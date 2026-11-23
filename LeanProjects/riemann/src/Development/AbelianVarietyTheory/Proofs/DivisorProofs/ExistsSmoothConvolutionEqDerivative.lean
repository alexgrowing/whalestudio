import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstFunctionalIntegralSmoothCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacePolynomialKernelDerivativeWordsFamilyStatement
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.LeftTranslate
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem foldr_rightDeriv_leftTranslate {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    (l : List 𝔤) (f : G → ℂ) (g : G) :
    l.foldr h.rightDeriv (fun y => f (g * y)) = fun x => l.foldr h.rightDeriv f (g * x) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons, ih]
    exact h.rightDeriv_leftTranslate X (l.foldr h.rightDeriv f) g

theorem exists_alpha_convolution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ l : List 𝔤, ∃ α : G → ℂ, h.IsSmoothFun α ∧ Continuous α ∧ HasCompactSupport α ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g, ∫ y, (f : G → ℂ) (g * y) * α y ∂μ = l.foldr h.rightDeriv (f : G → ℂ) g := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ l
  obtain ⟨hcont, hinv, K, hK, hfam⟩ := GlobalTheory.T.laplacePolynomialKernel_derivativeWords_family 𝔸 G 𝔤 h d b P hP μ hμ
  obtain ⟨α, hαs, hαc, hα⟩ := GlobalTheory.T.first_functional_integral_smooth_compact 𝔸 G 𝔤 h d b μ hμ (solG h b P) hcont hinv K hK _ (hfam l)
  refine ⟨α, hαs, ?_, hαc, ?_⟩
  · letI := h.chartedSpace
    exact hαs.continuous
  · intro f hf g
    have hmem : (f : G → ℂ) ∈ solG h b P := (mem_solG h b).2 ⟨f.2, hf⟩
    have h1 := hα _ (hinv _ hmem g)
    simp only [List.map_nil, List.nil_append] at h1
    rw [h1, foldr_rightDeriv_leftTranslate h l (f : G → ℂ) g]
    simp only [mul_one]

end GlobalTheory.HCA
