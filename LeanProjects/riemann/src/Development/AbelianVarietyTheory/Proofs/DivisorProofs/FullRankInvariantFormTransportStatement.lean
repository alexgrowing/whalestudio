import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankInvariantFormTransport
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullRank_invariant_form_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d), Ψ₁'.1 = GlobalTheory.FullRankCoinv.lact ν g Ψ₁.1 →
        Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
        (∀ (Y₁ Y₂ : Matrix (Fin n) (Fin d) k), Ψ₁.1 Y₁ ≠ 0 → Ψ₂.1 Y₂ ≠ 0 → ∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
        Bf Ψ₁ Ψ₂ = 0) →
      ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
        (∀ Y, Ψ₂.1 Y ≠ 0 → GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁.1 Y = 0) →
        Bf Ψ₁ Ψ₂ = 0 := by
  first | exact @GlobalTheory.FullRankCoinv.form_vanish_of_smallF_vanish | exact GlobalTheory.FullRankCoinv.form_vanish_of_smallF_vanish | (intros; apply GlobalTheory.FullRankCoinv.form_vanish_of_smallF_vanish <;> assumption)
