import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueFieldTilt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_field_tilt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (r : PreTilt O p →+* k), Function.Surjective r := by
  first | exact @GlobalTheory.TiltResidue.preTilt_onto_algClosed_residue | exact GlobalTheory.TiltResidue.preTilt_onto_algClosed_residue | (intros; apply GlobalTheory.TiltResidue.preTilt_onto_algClosed_residue <;> assumption)
