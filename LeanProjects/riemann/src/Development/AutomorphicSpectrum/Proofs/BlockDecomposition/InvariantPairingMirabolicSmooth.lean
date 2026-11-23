import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicEvaluationLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthInductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtensionStatement

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem pairing_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ]
        TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ,
      (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT hT' B hB hnd
  borelize k
  let ν : Measure k := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hinv : TwInv T T' B s := hB
  have hlin := GlobalTheory.T.mirabolic_evaluation_linear ν ψ T B hψ hT
  have hex := GlobalTheory.T.mirabolic_pairing_exists_eventual_value ν ψ c T T' B s hψ hc hT hT' hinv
  have huniq : ∀ {v v' A A'}, EvVal ν ψ T B v v' A → EvVal ν ψ T B v v' A' → A = A' := by
    rintro v v' A A' ⟨t₀, h₀⟩ ⟨t₁, h₁⟩
    rcases le_total (valuation k (t₀ : k)) (valuation k (t₁ : k)) with h | h
    · rw [← h₀ t₁ h, h₁ t₁ le_rfl]
    · rw [← h₀ t₀ le_rfl, h₁ t₀ h]
  choose f hf using hex
  let B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ f
    (fun v₁ v₂ v' => huniq (hf _ _) (hlin.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.1 _ _ _ _ (hf _ _)))
    (fun v v₁ v₂ => huniq (hf _ _) (hlin.2.2.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.2.2 _ _ _ _ (hf _ _)))
  have hB₀ : ∀ v v', B₀ v v' = f v v' := fun _ _ => rfl
  refine GlobalTheory.T.twisted_invariant_pairing_character ψ n s V V' T T' B₀ ?_ ?_ ?_ ?_
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_depth_induction ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).1
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_depth_induction ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).2
  · intro p v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_conductor_shift ν ψ c T T' B s hψ hc hT hT' hinv p v v' _ (hf _ _))
  · intro v hv
    obtain ⟨v', A, hA, hA0⟩ := GlobalTheory.T.mirabolic_pairing_conductor_extension ν ψ c T T' B s hψ hc hT hT' hinv hnd v hv
    exact ⟨v', by rw [hB₀, huniq (hf _ _) hA]; exact hA0⟩

end GlobalTheory.CompanionTheory.MirPair

end
