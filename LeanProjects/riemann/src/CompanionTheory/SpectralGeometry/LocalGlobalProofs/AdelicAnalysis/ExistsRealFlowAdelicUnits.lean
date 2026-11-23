import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealContinuousEmbeddingInfiniteAdelesStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Flow

theorem continuous_tmul_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (fun a : AF F => a ⊗ₜ[F] (1 : E)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  let φ : AF F →ₗ[AF F] AF F ⊗[F] E :=
    (TensorProduct.AlgebraTensorModule.mk F (AF F) (AF F) E).flip (1 : E)
  exact IsModuleTopology.continuous_of_linearMap φ

theorem exists_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ := by
  intro F E _ _ _ _ _ σ hCM
  obtain ⟨θ, hθ⟩ := (GlobalTheory.T.totally_real_continuous_embedding_infinite_adeles F hCM.1).1
  let g : ℝ → AF F ⊗[F] E := fun x => pairA F (θ (Real.exp x)) 1 ⊗ₜ[F] (1 : E)
  have g0 : g 0 = 1 := by
    simp only [g, Real.exp_zero, map_one]
    rfl
  have gadd : ∀ x y, g (x + y) = g x * g y := by
    intro x y
    have h : pairA F (θ (Real.exp x) * θ (Real.exp y)) 1 =
        pairA F (θ (Real.exp x)) 1 * pairA F (θ (Real.exp y)) 1 :=
      Prod.ext rfl (mul_one (1 : Af F)).symm
    simp only [g, Real.exp_add, map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, h]
  have gc : Continuous g := by
    refine (continuous_tmul_one F E).comp ?_
    show Continuous fun x : ℝ => ((θ (Real.exp x), 1) : AF F)
    exact (hθ.comp Real.continuous_exp).prodMk continuous_const
  let f : Multiplicative ℝ →* AF F ⊗[F] E :=
    { toFun := fun x => g x.toAdd
      map_one' := g0
      map_mul' := fun x y => gadd x.toAdd y.toAdd }
  refine ⟨f.toHomUnits, ?_, θ, hθ, fun x => rfl⟩
  rw [Units.continuous_iff]
  constructor
  · exact gc.comp continuous_toAdd
  · have : (fun x : Multiplicative ℝ => (((f.toHomUnits x)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) =
        fun x => g (-x.toAdd) := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact gc.comp (continuous_neg.comp continuous_toAdd)

end GlobalTheory.CompanionTheory.SW.Flow
