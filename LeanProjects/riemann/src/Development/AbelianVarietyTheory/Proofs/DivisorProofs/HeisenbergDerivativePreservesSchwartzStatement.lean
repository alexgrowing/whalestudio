import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativePreservesSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_derivative_preserves_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ w : (κ → AF F) × (κ → AF F), IsArch w → ∀ Φ ∈ schA F κ, dH ψ w Φ ∈ schA F κ := by
  first | exact @GlobalTheory.ThetaDecay.dH_mem_schA | exact GlobalTheory.ThetaDecay.dH_mem_schA | (intros; apply GlobalTheory.ThetaDecay.dH_mem_schA <;> assumption)
