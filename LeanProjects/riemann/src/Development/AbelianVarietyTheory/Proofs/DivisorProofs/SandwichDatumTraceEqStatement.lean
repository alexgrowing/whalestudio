import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumTraceEq
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwich_datum_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ) (a : Λ), (actH D a).trace = (actT D a).trace ∧ (actT D a).trace = padicToO p O (D.ρT a).trace := by
  first | exact @GlobalTheory.trace_actH_eq_trace_actT | exact GlobalTheory.trace_actH_eq_trace_actT | (intros; apply GlobalTheory.trace_actH_eq_trace_actT <;> assumption)
