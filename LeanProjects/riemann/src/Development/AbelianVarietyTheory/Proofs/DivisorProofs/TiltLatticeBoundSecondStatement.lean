import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLatticeBoundSecond
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_lattice_bound_second : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
      [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N →
      ∀ (D : GlobalTheory.Sandwich.Datum ε h Λ) (τ : Λ →+* O),
        (∃! ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι) ∧
          ∀ ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι → Function.Bijective ι := by
  first | exact @GlobalTheory.IotaDet.iota_existsUnique_bijective | exact GlobalTheory.IotaDet.iota_existsUnique_bijective | (intros; apply GlobalTheory.IotaDet.iota_existsUnique_bijective <;> assumption)
