import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentInvariantFunctionalTwoDim
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_invariant_functional_two_dim : (GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ), 1 ≤ n → 2 * n < d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
  ∀ ℓ : (GL (Fin d) k → ℂ) →ₗ[ℂ] ℂ,
    (∀ u : GL (Fin d) k, GlobalTheory.JacBlock₂.IsUnipStd u → ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ℓ (fun h => f (h * u)) = ℓ f) →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ p q : ℂ, ∀ x : kˣ,
      ℓ (fun h => f (h * GlobalTheory.JacBlock₂.diagFirst x)) = p + q * (((ν x)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow x (((d : ℂ) - 2 * (n : ℂ)) / 2)) → (GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ), 1 ≤ n → 2 * n < d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
  ∀ Λ₀ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ,
    (∀ (g : GL (Fin n) k), ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), Λ₀ (GlobalTheory.FullRankCoinv.lact ν g Ψ - Ψ) = 0) →
    (∀ u : GL (Fin d) k, GlobalTheory.JacBlock₂.IsUnipStd u → ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), Λ₀ (fun Y => Ψ (Y * u.1)) = Λ₀ Ψ) →
    (∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
      Ψ - Ψ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin n) k) (Ψ' : Matrix (Fin n) (Fin d) k → ℂ),
        Ψ' ∈ SB (Matrix (Fin n) (Fin d) k) ∧ z = GlobalTheory.FullRankCoinv.lact ν g Ψ' - Ψ'}) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ p q : ℂ, ∀ x : kˣ,
      Λ₀ (fun Y => Ψ (Y * (GlobalTheory.JacBlock₂.diagFirst x).1)) = p + q * (((ν x)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow x (((d : ℂ) - 2 * (n : ℂ)) / 2)) := by
  first | exact @GlobalTheory.FullRankCoinv.JacReduce.jac_reduce | exact GlobalTheory.FullRankCoinv.JacReduce.jac_reduce | (intros; apply GlobalTheory.FullRankCoinv.JacReduce.jac_reduce <;> assumption)
