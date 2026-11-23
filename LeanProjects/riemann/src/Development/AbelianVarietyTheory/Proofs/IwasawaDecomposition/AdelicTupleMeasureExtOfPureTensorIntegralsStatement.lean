import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTupleMeasureExtOfPureTensorIntegrals
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (n M : ℕ) (ν ν' : Measure (Fin n → Fin M → AF F ⊗[F] E)), (∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Integrable Φ ν' ∧ ∫ X, Φ X ∂ν = ∫ X, Φ X ∂ν') → ν = ν' := by
  first | exact @GlobalTheory.GaugeEx.PureUniq.measure_ext_of_pure | exact GlobalTheory.GaugeEx.PureUniq.measure_ext_of_pure | (intros; apply GlobalTheory.GaugeEx.PureUniq.measure_ext_of_pure <;> assumption)
