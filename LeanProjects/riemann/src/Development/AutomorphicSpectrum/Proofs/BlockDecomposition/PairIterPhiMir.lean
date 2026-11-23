import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmooth

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZPairDescend

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 2000000 in

theorem pair_iterPhi_mir (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) :
    ∀ (j s : ℕ) (τ τ' : MRep k (n + 1 + j)),
    IsSmooth τ.ρ → IsSmooth τ'.ρ → ∀ B : τ.V →ₗ[ℂ] τ'.V →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1 + j)) v v', B (τ.ρ p v) (τ'.ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : (iterPhi k ψ j τ).V →ₗ[ℂ] (iterPhi k ψ⁻¹ j τ').V →ₗ[ℂ] ℂ,
      (∀ (p : Mir k (n + 1)) w w', B' ((iterPhi k ψ j τ).ρ p w) ((iterPhi k ψ⁻¹ j τ').ρ p w') =
        ((detChar (Fin (n + 1 + 1)) (absPow k ((s + j : ℕ) : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0)
  | 0, s, _, _, _, _, B, hB, hn => ⟨B, hB, hn⟩
  | j + 1, s, τ, τ', hs, hs', B, hB, hn => by
    obtain ⟨B₁, hB₁, hn₁⟩ := GlobalTheory.CompanionTheory.MirPair.pairing_phi k ψ hc h1 (n + 1 + j) s _ _ τ.ρ τ'.ρ hs hs' B hB hn
    obtain ⟨B₂, hB₂, hn₂⟩ := pair_iterPhi_mir ψ hc h1 n j (s + 1) (MRep.phiM k ψ τ) (MRep.phiM k ψ⁻¹ τ')
      (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hs) (GlobalTheory.T.smooth_phi_minus k ψ⁻¹ _ _ _ hs') B₁ hB₁ hn₁
    refine ⟨B₂, fun p w w' => ?_, hn₂⟩
    have e : s + (j + 1) = s + 1 + j := by omega
    rw [e]
    exact hB₂ p w w'

set_option maxHeartbeats 2000000 in

theorem pair_iterPhi (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V V' : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (π' : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V') (hs : IsSmooth π) (hs' : IsSmooth π')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π g v) (π' g v') = B v v') (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) :
    ∃ B' : (iterPhi k ψ j (resM k π)).V →ₗ[ℂ] (iterPhi k ψ⁻¹ j (resM k π')).V →ₗ[ℂ] ℂ,
      (∀ (p : Mir k (n + 1)) w w', B' ((iterPhi k ψ j (resM k π)).ρ p w) ((iterPhi k ψ⁻¹ j (resM k π')).ρ p w') =
        ((detChar (Fin (n + 1 + 1)) (absPow k (j : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  have hB0 : ∀ (p : Mir k (n + 1 + j)) v v', B ((resM k π).ρ p v) ((resM k π').ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k ((0 : ℕ) : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v' := by
    intro p v v'
    rw [GlobalTheory.CompanionTheory.BZCuspPair.detChar_zero, one_mul]
    exact hB (p : GL (Fin (n + 1 + j + 1)) k) v v'
  obtain ⟨B', h2, h3⟩ := pair_iterPhi_mir ψ hc h1 n j 0 (resM k π) (resM k π')
    (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_resM hs) (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_resM hs') B hB0 hn
  refine ⟨B', fun p w w' => ?_, h3⟩
  have := h2 p w w'
  rwa [Nat.zero_add] at this

end GlobalTheory.CompanionTheory.BZPairDescend

end
