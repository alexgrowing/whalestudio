import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepOpIndefOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIwasawaOfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetConvolutionContinuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyReal
import Development.AbelianVarietyTheory.Definitions.Divisors.SecSpaceBotNeBot

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF GlobalTheory.SWOpCase

namespace GlobalTheory.SWOpIndef

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

def supAt {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) (v₀ : HeightOneSpectrum (𝓞 F)) : Subgroup (UA σ J₂) where
  carrier := {g | (mat g).det = 1 ∧ (∀ v, v ≠ v₀ → (mat g).map (compFin F E v) = 1) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (mat g).map (piInf τ) = 1}
  one_mem' := by
    refine ⟨by simp [show mat (1 : UA σ J₂) = 1 from rfl], fun v _ => ?_, fun w τ => ?_⟩ <;>
      simp [show mat (1 : UA σ J₂) = 1 from rfl]
  mul_mem' := by
    rintro g h ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    have e : mat (g * h) = mat g * mat h := rfl
    refine ⟨by rw [e, Matrix.det_mul, h1, h1', one_mul], fun v hv => ?_, fun w τ => ?_⟩
    · rw [e, Matrix.map_mul, h2 v hv, h2' v hv, one_mul]
    · rw [e, Matrix.map_mul, h3 w τ, h3' w τ, one_mul]
  inv_mem' := by
    rintro g ⟨h1, h2, h3⟩
    have e : mat g⁻¹ * mat g = 1 := by
      change mat (g⁻¹ * g) = 1
      rw [inv_mul_cancel]; rfl
    refine ⟨?_, fun v hv => ?_, fun w τ => ?_⟩
    · have := congrArg Matrix.det e
      rwa [Matrix.det_mul, h1, mul_one, Matrix.det_one] at this
    · have := congrArg (fun M => M.map (compFin F E v)) e
      simp only [Matrix.map_mul, h2 v hv, mul_one] at this
      simpa using this
    · have := congrArg (fun M => M.map (piInf τ)) e
      simp only [Matrix.map_mul, h3 w τ, mul_one] at this
      simpa using this

def IsAnisoAt {m : ℕ} (JV : Matrix (Fin m) (Fin m) E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : Fin m → Fv F v ⊗[F] E,
    x ⬝ᵥ (JV.map (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E)) *ᵥ
      (fun i => Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (x i)) = 0 → x = 0

example {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) (g h : UA σ J₂) : mat (g * h) = mat g * mat h := by rfl
example {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) : mat (1 : UA σ J₂) = 1 := by rfl

end GlobalTheory.SWOpIndef
