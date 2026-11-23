import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNormalizedLocalHaarSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_normalizedLocalHaar_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, SdR (Fv F v) (psiV F ψ v) (s.nuV v) ∧ SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (tupMeas (s.lamV v) 1 M) := by
  first | exact @GlobalTheory.GaugeEx.SelfDualAE.main | exact GlobalTheory.GaugeEx.SelfDualAE.main | (intros; apply GlobalTheory.GaugeEx.SelfDualAE.main <;> assumption)
