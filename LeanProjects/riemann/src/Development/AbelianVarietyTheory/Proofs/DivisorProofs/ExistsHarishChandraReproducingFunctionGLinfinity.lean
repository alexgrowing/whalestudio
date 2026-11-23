import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConvolutionEqDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacianStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic

namespace GlobalTheory.HCAlphaGLC

section

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def topE : glG E a ≃ₜ* GL (Fin a) (Cinf E) where
  toMulEquiv := Subgroup.topEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧ HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
  intro E _ _ _ a L _ W hW X hX N _ _ μ hμ
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite E a L W hW X hX N
  obtain ⟨d, b, P, hPm, -, hP⟩ := GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian E a p hp0
  let e := topE E a
  letI : MeasurableSpace (glG E a) := borel _
  haveI : BorelSpace (glG E a) := ⟨rfl⟩
  let μ' : Measure (glG E a) := μ.map e.symm
  have hH : μ'.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  obtain ⟨α', -, hc, hs, hα⟩ := @GlobalTheory.T.exists_smooth_convolution_eq_derivative (Matrix (Fin a) (Fin a) (Cinf E)) _ _ _ _ (glG E a) (glL E a) (glH E a) d b P hPm _ (by exact ⟨rfl⟩) μ' (by exact hH) []
  refine ⟨α' ∘ e.symm, ?_, ?_, fun φ hφ g => ?_⟩
  · exact hc.comp e.symm.continuous
  · exact hs.comp_homeomorph e.symm.toHomeomorph
  obtain ⟨hf, h0⟩ := (mem_solG _ _).1 (hP φ (hp φ hφ) g)
  have h1 := hα ⟨_, hf⟩ h0 1
  have hm : μ' = μ.map e.symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [hm, integral_map_equiv] at h1
  simp only [one_mul, List.foldr_nil] at h1
  exact h1.trans (by simp [glRes])

end

end GlobalTheory.HCAlphaGLC

end
