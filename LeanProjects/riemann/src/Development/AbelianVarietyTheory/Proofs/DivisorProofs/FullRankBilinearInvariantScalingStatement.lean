import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankBilinearInvariantScaling
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_bilinear_invariant_scaling : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ) (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ), (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : fullRk k n d), Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) → (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' : fullRk k n d, Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) → ∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (B₁ B₂ : Set (Matrix (Fin n) (Fin d) k)), ∃ r : ℝ, 0 < r ∧ pv Bf {Y | (g.1)ᵀ * Y * h.1 ∈ B₁} {Y | Y * h.1 ∈ B₂} = (r : ℂ) * ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2))⁻¹ * pv Bf B₁ B₂ := by
  first | exact @GlobalTheory.NormalCore.pv_transport | exact GlobalTheory.NormalCore.pv_transport | (intros; apply GlobalTheory.NormalCore.pv_transport <;> assumption)
