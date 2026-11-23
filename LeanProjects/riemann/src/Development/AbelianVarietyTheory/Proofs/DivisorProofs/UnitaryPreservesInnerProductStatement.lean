import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPreservesInnerProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_preserves_inner_product : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ φ ∈ schA F κ, T φ ∈ schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ φ ∈ schA F κ,
      ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f ∈ schA F κ, ∀ g ∈ schA F κ,
      ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  first | exact @GlobalTheory.L2PairingPolar.pairing_eq | exact GlobalTheory.L2PairingPolar.pairing_eq | (intros; apply GlobalTheory.L2PairingPolar.pairing_eq <;> assumption)
