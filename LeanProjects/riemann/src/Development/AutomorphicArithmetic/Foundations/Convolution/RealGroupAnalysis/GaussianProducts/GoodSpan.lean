import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.goodSpan :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), Good D 0 ∧ (∀ Φ Φ', Good D Φ → Good D Φ' → Good D (Φ + Φ')) ∧ ∀ (c : ℂ) Φ, Good D Φ → Good D (c • Φ) := by
  intro F E _ _ _ _ _ D
  have hWE : ∀ (Φ : GL (Fin 2) (A E) → ℂ) h,
      WE D Φ h = ∫ u in FS2 F, Φ (nE D u * h) * ψ (2 * u 0) ∂(adeleMeasurePi F) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ _ => rfl, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun h => ?_⟩
    · simpa using (integrableOn_zero (μ := adeleMeasurePi F) (s := FS2 F))
    · simpa using (integrableOn_zero (μ := adeleMeasurePi F) (s := FS2 F))
    · simp
    · have : ∀ ξ : Rw F, WE D (0 : GL (Fin 2) (A E) → ℂ) (aE (al D ξ.1) * h) = 0 := by
        intro ξ
        rw [hWE]
        simp
      simp only [this]
      exact hasSum_zero
  · intro Φ Φ' h1 h2
    refine ⟨fun γ h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Pi.add_apply, h1.left, h2.left]
    · exact (h1.int0 h).add (h2.int0 h)
    · have heq : (fun u => (Φ + Φ') (nE D u * h) * ψ (2 * u 0))
          = (fun u => Φ (nE D u * h) * ψ (2 * u 0)) + fun u => Φ' (nE D u * h) * ψ (2 * u 0) := by
        funext u
        simp only [Pi.add_apply, add_mul]
      rw [heq]
      exact (h1.int1 h).add (h2.int1 h)
    · simp only [Pi.add_apply]
      rw [integral_add (h1.int0 h) (h2.int0 h), h1.zero, h2.zero, add_zero]
    · have : ∀ ξ : Rw F, WE D (Φ + Φ') (aE (al D ξ.1) * h)
          = WE D Φ (aE (al D ξ.1) * h) + WE D Φ' (aE (al D ξ.1) * h) := by
        intro ξ
        simp only [hWE, Pi.add_apply, add_mul]
        exact integral_add (h1.int1 _) (h2.int1 _)
      simp only [this, Pi.add_apply]
      exact (h1.sum h).add (h2.sum h)
  · intro c Φ h1
    refine ⟨fun γ h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Pi.smul_apply, h1.left]
    · exact (h1.int0 h).const_mul c
    · have heq : (fun u => (c • Φ) (nE D u * h) * ψ (2 * u 0))
          = fun u => c * (Φ (nE D u * h) * ψ (2 * u 0)) := by
        funext u
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [heq]
      exact (h1.int1 h).const_mul c
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [integral_const_mul, h1.zero, mul_zero]
    · have : ∀ ξ : Rw F, WE D (c • Φ) (aE (al D ξ.1) * h) = c * WE D Φ (aE (al D ξ.1) * h) := by
        intro ξ
        simp only [hWE, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul _ _
      simp only [this, Pi.smul_apply, smul_eq_mul]
      exact (h1.sum h).mul_left c
