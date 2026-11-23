import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEmbeddingContinuousRational
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_embedding_continuous_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (J₂ : Matrix (Fin (d + d)) (Fin (d + d)) E),
    ∀ i : UA σ J × UA σ J →* UA σ J₂, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
      Continuous i ∧ ∀ δ ∈ ratU σ J, i (1, δ) ∈ ratU σ J₂ := by
  first | exact @GlobalTheory.DoublingCont.continuous_and_rat | exact GlobalTheory.DoublingCont.continuous_and_rat | (intros; apply GlobalTheory.DoublingCont.continuous_and_rat <;> assumption)
