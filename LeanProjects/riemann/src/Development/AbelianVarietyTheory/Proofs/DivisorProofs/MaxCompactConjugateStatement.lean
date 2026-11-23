import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.max_compact_conjugate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K₁ K₂ : Subgroup (GAd σ J),
      GlobalTheory.UAut.IsMaxCpt σ J K₁ → GlobalTheory.UAut.IsMaxCpt σ J K₂ → ∃ a ∈ GlobalTheory.AdelicU.infPts σ J, ∀ k, k ∈ K₂ ↔ a * k * a⁻¹ ∈ K₁ := by
  first | exact @GlobalTheory.MaxCptConj.isMaxCpt_conj | exact GlobalTheory.MaxCptConj.isMaxCpt_conj | (intros; apply GlobalTheory.MaxCptConj.isMaxCpt_conj <;> assumption)
