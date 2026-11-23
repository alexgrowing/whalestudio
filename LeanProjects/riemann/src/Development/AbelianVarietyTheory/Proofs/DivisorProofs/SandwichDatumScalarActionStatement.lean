import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwich_datum_scalar_action : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ), (∀ c : ℤ_[p], D.ρM (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) ∧ D.F * D.G = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ (∀ l, D.G * D.ρM l = rhoTA D l * D.G) ∧ (∀ l, D.Ψ * (D.ρM l).map (phiInv p O) = D.ρM l * D.Ψ) ∧ ∀ l, D.Ψ' * D.ρM l = (D.ρM l).map (phiInv p O) * D.Ψ' := by
  first | exact @GlobalTheory.DetInv.datum_scalar_intertwine | exact GlobalTheory.DetInv.datum_scalar_intertwine | (intros; apply GlobalTheory.DetInv.datum_scalar_intertwine <;> assumption)
