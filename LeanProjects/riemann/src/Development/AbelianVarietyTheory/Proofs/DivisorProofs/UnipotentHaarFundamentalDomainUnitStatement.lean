import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarFundamentalDomainUnit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAutSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_haar_fundamental_domain_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n n₁ : ℕ}
    (Y : Spc F E n) (H : Plane E n n₁),
    (∃ K : Set (unip σ Y H), IsCompact K ∧ ∀ u : unip σ Y H, ∃ γ ∈ (ratU σ Y.J).subgroupOf (unip σ Y H), γ * u ∈ K) →
    ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.UnipFD.main | exact GlobalTheory.UnipFD.main | (intros; apply GlobalTheory.UnipFD.main <;> assumption)
