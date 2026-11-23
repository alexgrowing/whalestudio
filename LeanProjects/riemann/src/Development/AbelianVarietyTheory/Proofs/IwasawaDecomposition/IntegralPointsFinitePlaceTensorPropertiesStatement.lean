import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralPointsFinitePlaceTensor_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ v : HeightOneSpectrum (𝓞 F), IsCompact (intV b v) ∧ IsOpen (intV b v)) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : Fv F v ⊗[F] E) ∈ intV b v ∧ (∀ y ∈ intV b v, ∀ z ∈ intV b v, y * z ∈ intV b v) ∧ ∀ y ∈ intV b v, sigR (Fv F v) σ y ∈ intV b v) ∧ (∀ z : AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, prV v z ∈ intV b v) ∧ ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, intV b v = intV b' v := by
  first | exact @GlobalTheory.GaugeEx.IntBasis.main | exact GlobalTheory.GaugeEx.IntBasis.main | (intros; apply GlobalTheory.GaugeEx.IntBasis.main <;> assumption)
