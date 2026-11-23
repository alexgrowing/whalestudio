import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundLinearCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_bound_linear_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (f : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F)), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ), 0 ≤ B →
    (∀ w k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ B) →
    ∀ w i, ‖archAt F w ((f x).1 i)‖ ≤ K * B ∧ ‖archAt F w ((f x).2 i)‖ ≤ K * B := by
  first | exact @GlobalTheory.ThetaDecay.arch_bound_pair | exact GlobalTheory.ThetaDecay.arch_bound_pair | (intros; apply GlobalTheory.ThetaDecay.arch_bound_pair <;> assumption)
