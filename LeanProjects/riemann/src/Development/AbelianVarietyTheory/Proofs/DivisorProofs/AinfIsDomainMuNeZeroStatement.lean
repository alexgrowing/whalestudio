import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfIsDomainMuNeZero
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_isDomain_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → IsDomain (Ainf p O) ∧ mu ε ≠ 0 := by
  first | exact @GlobalTheory.ainf_isDomain_and_mu_ne_zero | exact GlobalTheory.ainf_isDomain_and_mu_ne_zero | (intros; apply GlobalTheory.ainf_isDomain_and_mu_ne_zero <;> assumption)
