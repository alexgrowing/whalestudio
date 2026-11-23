import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompact
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureFiniteAdelicTestFunction_continuous_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d M n : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), IsPureFin b Φf Φv → Continuous Φf ∧ HasCompactSupport Φf := by
  first | exact @GlobalTheory.isPureFin_continuous_hasCompactSupport | exact GlobalTheory.isPureFin_continuous_hasCompactSupport | (intros; apply GlobalTheory.isPureFin_continuous_hasCompactSupport <;> assumption)
