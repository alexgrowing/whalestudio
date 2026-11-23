import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportCompactModParabolicOffClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_compact_mod_parabolic_off_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ C : Set (Mir k ((i + 1) + t + 1)), IsCompact C ∧ (∀ c ∈ C, c ∉ Cl k i t) ∧
    ∀ g, evX f g ≠ 0 → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ c ∈ C, g = h * c := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl | exact GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off_Cl <;> assumption)
