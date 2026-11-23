import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInvariantFunctionalDetPower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_invariant_functional_det_power : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n < d →
    ∀ Λ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ,
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
        (m : ℂ) * Λ (fun Y => φ (Y * h.1)) = Λ φ) →
      ∀ (g : GL (Fin n) k), ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (d : ℂ) * Λ (fun Y => φ ((g.1)ᵀ * Y)) = Λ φ := by
  first | exact @GlobalTheory.FullRankCoinv.LeftScale.left_scale | exact GlobalTheory.FullRankCoinv.LeftScale.left_scale | (intros; apply GlobalTheory.FullRankCoinv.LeftScale.left_scale <;> assumption)
