import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTorusCommutative
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_torus_commutative : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ), (∀ a ∈ PositivityTheory.Lbc.Tor k N, ∀ b ∈ PositivityTheory.Lbc.Tor k N, a * b = b * a) ∧ ∀ x : GL (Fin N) k, x ∈ PositivityTheory.Lbc.Tor k N ↔ ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LbElem.TorComm.tor_comm_and_mem_iff | exact GlobalTheory.CompanionTheory.LbElem.TorComm.tor_comm_and_mem_iff | (intros; apply GlobalTheory.CompanionTheory.LbElem.TorComm.tor_comm_and_mem_iff <;> assumption)
