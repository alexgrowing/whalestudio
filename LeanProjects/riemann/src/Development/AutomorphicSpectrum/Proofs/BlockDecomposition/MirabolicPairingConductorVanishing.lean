import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem exists_evVal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (v : V) (v' : V'), ∃ A, EvVal ν ψ T B v v' A := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB v v'
  obtain ⟨r, hr⟩ := GlobalTheory.T.mirabolic_pairing_conductor_bound ν ψ c T T' B s hψ hc hT hT' hB 1 v v'
  refine ⟨JJ ν ψ T B (box (n + 1) (c * r⁻¹) : Set (Fin (n + 1) → k)) v v', c * r⁻¹, fun t ht => ?_⟩
  have hc' : valuation k ((c * (c * r⁻¹)⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
    have : c * (c * r⁻¹)⁻¹ = r := by
      rw [_root_.mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
    rw [this]
  have hsub : ∀ x ∈ box (n + 1) (c * r⁻¹), ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t := by
    intro x hx
    rw [Units.val_one, one_mulVec]
    rw [mem_box] at hx ⊢
    exact fun i => show valuation k (x i) ≤ valuation k (t : k) from
      le_trans (show valuation k (x i) ≤ valuation k ((c * r⁻¹ : kˣ) : k) from hx i) ht
  have h := hr (c * r⁻¹) hc' t hsub
  rw [← h]
  simp only [Units.val_one, one_mulVec]
  rfl

end GlobalTheory.CompanionTheory.MirPair
