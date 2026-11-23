import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_log_hom_is_multiple_of_log_abs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (φ : (AE F E)ˣ → ℂ), Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) → (∀ γ : Eˣ, φ (Units.map (inclR (F := F) (AF F)).toMonoidHom γ) = 0) → ∃ A : ℂ, ∀ t, φ t = A * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.IdeleLogHom.exists_eq_mul_log_absE | exact GlobalTheory.IdeleLogHom.exists_eq_mul_log_absE | (intros; apply GlobalTheory.IdeleLogHom.exists_eq_mul_log_absE <;> assumption)
