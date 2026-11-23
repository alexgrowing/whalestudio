import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFunctionRadialLogDependence
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
theorem _root_.GlobalTheory.T.invariant_function_radial_log_dependence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ φ : (AE F E)ˣ → ℂ, Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) → (∀ γ : Eˣ, φ (Units.map (inclR (F := F) (AF F)).toMonoidHom γ) = 0) → ∃ A : ℂ, ∀ t, φ t = A * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ)) → ∀ (Fn : (AE F E)ˣ → ℂ), Continuous Fn → (∀ (γ : Eˣ) (t : (AE F E)ˣ), Fn (Units.map (inclR (F := F) (AF F)).toMonoidHom γ * t) = Fn t) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : (AE F E)ˣ => fun t => Fn (t * s))) → ∃ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ ∧ ∀ t : (AE F E)ˣ, Fn t = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ) := by
  first | exact @GlobalTheory.AbExp.main | exact GlobalTheory.AbExp.main | (intros; apply GlobalTheory.AbExp.main <;> assumption)
