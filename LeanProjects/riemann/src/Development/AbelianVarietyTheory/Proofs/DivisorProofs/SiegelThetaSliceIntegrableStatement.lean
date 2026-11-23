import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaSliceIntegrable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_theta_slice_integrable : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : Type) [Fintype m]
    [DecidableEq m] (B : (m → F) →ₗ[F] (κ → F)), Function.Injective B →
    ∀ μ : @Measure (m → AF F) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ φ ∈ schA F κ, (letI : MeasurableSpace (m → AF F) := borel _;
      Integrable (fun t : m → AF F => φ (fun i => ∑ j, t j * algebraMap F (AF F) (B (Pi.single j 1) i))) μ) := by
  first | exact @GlobalTheory.CompInjInt.main | exact GlobalTheory.CompInjInt.main | (intros; apply GlobalTheory.CompInjInt.main <;> assumption)
