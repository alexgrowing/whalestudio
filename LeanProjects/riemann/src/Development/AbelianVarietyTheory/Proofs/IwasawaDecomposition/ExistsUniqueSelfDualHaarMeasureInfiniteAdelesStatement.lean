import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_selfDual_haar_measure_infinite_adeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∃! ν, SdR (Ainf F) (psiInf F ψ) ν) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃! μ, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μ := by
  first | exact @GlobalTheory.GaugeEx.SdInf.existsUnique_selfDual_inf | exact GlobalTheory.GaugeEx.SdInf.existsUnique_selfDual_inf | (intros; apply GlobalTheory.GaugeEx.SdInf.existsUnique_selfDual_inf <;> assumption)
