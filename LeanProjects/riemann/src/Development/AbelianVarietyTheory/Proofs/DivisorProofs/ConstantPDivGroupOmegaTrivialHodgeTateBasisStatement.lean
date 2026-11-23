import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantPDivGroupOmegaTrivialHodgeTateBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantPDivGroup_omega_trivial_hodgeTate_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, IsConst G → Subsingleton G.omega ∧ ∀ (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate), Function.Bijective (Fintype.linearCombination O fun i => hodgeTate G (b i)) := by
  first | exact @GlobalTheory.ConstHT.omega_const | exact GlobalTheory.ConstHT.omega_const | (intros; apply GlobalTheory.ConstHT.omega_const <;> assumption)
