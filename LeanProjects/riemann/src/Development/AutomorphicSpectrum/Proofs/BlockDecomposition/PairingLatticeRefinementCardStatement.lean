import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingLatticeRefinementCard
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_lattice_refinement_card : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ), (∀ x f f', B (shiftF x f) (shiftF x f') = B f f') → ∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → ∀ (x : Fin d → k) (a : V) (a' : V'), mL B L x a a' = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.mL_refine | exact GlobalTheory.CompanionTheory.BZCore.mL_refine | (intros; apply GlobalTheory.CompanionTheory.BZCore.mL_refine <;> assumption)
