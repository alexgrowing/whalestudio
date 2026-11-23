import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFourier_realises_weylElement : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ ε : κ → ℤˣ, ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp ψ (fun w => (fun i => ((ε i : ℤ) : AF F) * w.2 i, fun i => -(((ε i : ℤ) : AF F) * w.1 i))) S S' ∧ ∀ φ ∈ schA F κ, ∀ y, S φ y = ∫ x, φ x * ψ (∑ i, ((ε i : ℤ) : AF F) * x i * y i) ∂μ := by
  first | exact @GlobalTheory.TowU.FourWeyl.isOp_fourier | exact GlobalTheory.TowU.FourWeyl.isOp_fourier | (intros; apply GlobalTheory.TowU.FourWeyl.isOp_fourier <;> assumption)
