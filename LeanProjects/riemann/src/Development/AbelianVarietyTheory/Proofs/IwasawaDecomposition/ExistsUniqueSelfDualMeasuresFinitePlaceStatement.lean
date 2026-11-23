import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_selfDual_measures_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), (∃! ν, SdR (Fv F v) (psiV F ψ v) ν) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃! μ, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 μ := by
  first | exact @GlobalTheory.SelfDualFinite.existsUnique_selfDual_finite | exact GlobalTheory.SelfDualFinite.existsUnique_selfDual_finite | (intros; apply GlobalTheory.SelfDualFinite.existsUnique_selfDual_finite <;> assumption)
