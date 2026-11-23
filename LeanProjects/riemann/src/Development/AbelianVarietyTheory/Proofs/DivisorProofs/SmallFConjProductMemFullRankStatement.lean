import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallFConjProductMemFullRank
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallF_conj_product_mem_fullRank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ₁ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Ψ₂ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
      (fun Y => GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁ Y * (starRingEnd ℂ) (Ψ₂ Y))
        ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
  first | exact @GlobalTheory.FullRankCoinv.smallF_mul_conj_mem_fullRk | exact GlobalTheory.FullRankCoinv.smallF_mul_conj_mem_fullRk | (intros; apply GlobalTheory.FullRankCoinv.smallF_mul_conj_mem_fullRk <;> assumption)
