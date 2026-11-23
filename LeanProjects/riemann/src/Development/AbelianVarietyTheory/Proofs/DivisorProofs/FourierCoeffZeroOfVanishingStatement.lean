import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoeffZeroOfVanishing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_coeff_zero_of_vanishing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n : ℕ) (a : (Fin n → E) → ℂ), Summable a → (∀ z : Fin n → AE F E, ∑' ξ : Fin n → E, ψ (Algebra.trace (AF F) (AE F E) (∑ i, incV F ξ i * z i)) * a ξ = 0) → a 0 = 0 := by
  first | exact @GlobalTheory.FourierIsolation.coeff_zero_eq_zero | exact GlobalTheory.FourierIsolation.coeff_zero_eq_zero | (intros; apply GlobalTheory.FourierIsolation.coeff_zero_eq_zero <;> assumption)
