import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveIntoLineSpanEqSmulSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLatticePrincipalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLatticeBoundSecondStatement

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.DetLattice

theorem iota_image_detLattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
      [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N →
      ∀ (D : GlobalTheory.Sandwich.Datum ε h Λ) (τ : Λ →+* O) ι, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.IsIota C D τ N ι →
        ∃ lam : C, lam ≠ 0 ∧
          ι '' (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLattice C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D) τ N : Set (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLine C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actT D) τ N)) =
            (fun w => lam • w) '' (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLattice C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D) τ N : Set (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.detLine C (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.actH D) τ N)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D τ ι hι
  obtain ⟨⟨hTi, hTs, hTd⟩, ⟨hHi, hHs, hHd⟩⟩ := GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  obtain ⟨-, x, hx0, hxL⟩ := GlobalTheory.T.determinant_lattice_principal C v O Λ h N hv (actT D) τ hTi hTs (hTd τ)
  obtain ⟨hW, y, hy0, hyL⟩ := GlobalTheory.T.determinant_lattice_principal C v O Λ h N hv (actH D) τ hHi hHs (hHd τ)
  have hbij := (GlobalTheory.T.tilt_lattice_bound_second p C v O hv ε hε Λ N h hh D τ).2 ι hι
  obtain ⟨lam, hlam, -, himg⟩ :=
    GlobalTheory.injective_into_line_span_eq_smul_span C O _ _ ι x y hbij.1 hW hx0 hy0
  exact ⟨lam, hlam, by rw [hxL, hyL]; exact himg⟩

end GlobalTheory.DetLattice
