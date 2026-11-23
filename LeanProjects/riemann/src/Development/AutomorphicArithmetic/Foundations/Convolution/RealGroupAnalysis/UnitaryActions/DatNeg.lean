import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.datNeg :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex E] (δ : F) (θ : E) (b : Module.Basis (Fin 2) F E),
      b 0 = 1 → b 1 = θ → θ ^ 2 = algebraMap F E δ → ∀ φ : F →+* ℝ, φ δ < 0 := by
  intro F E _ _ _ _ _ _ δ θ b h0 h1 hθ φ
  by_contra hneg
  have hpos : 0 ≤ φ δ := not_lt.mp hneg
  haveI : Module.Finite F E := Module.Finite.of_basis b
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  let ψ : F →+* ℂ := Complex.ofRealHom.comp φ
  let τ : E →+* ℂ := NumberField.ComplexEmbedding.lift E ψ
  have hτ : ∀ x : F, τ (algebraMap F E x) = ((φ x : ℝ) : ℂ) := by
    intro x
    exact NumberField.ComplexEmbedding.lift_algebraMap_apply E ψ x
  have hsq : (τ θ) ^ 2 = ((Real.sqrt (φ δ) : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hθ, hτ, ← Complex.ofReal_pow, Real.sq_sqrt hpos]
  have hreal : (starRingEnd ℂ) (τ θ) = τ θ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [h, Complex.conj_ofReal]
    · rw [h, map_neg, Complex.conj_ofReal]
  have hall : ∀ z : E, (starRingEnd ℂ) (τ z) = τ z := by
    intro z
    have hz := b.sum_repr z
    rw [Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def] at hz
    rw [← hz]
    simp only [map_add, map_mul, map_one, hτ, Complex.conj_ofReal, hreal]
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext z
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  exact hall z
