import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSectionPeriodicity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_section_periodicity : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ}
    (hB : IsOpen B) (hj : IsFactor B τ M j) {b : E} (hb : b ∈ B) {m : ℕ}
    (f : (Fin g → ℂ) → Ext m) (hf : IsSec τ M j b f) (l : Fl g) (hl : l ∈ M) (z : Fin g → ℂ)
    (c : Fin g) (S : Finset (Fin m)),
    d01 (fun z' => f z' S) (z + per (τ b) l) (ev c) = j l (b, z) * d01 (fun z' => f z' S) z (ev c) := by
  first | exact @GlobalTheory.FlatAcycShift.dbar_coeff_transl | exact GlobalTheory.FlatAcycShift.dbar_coeff_transl | (intros; apply GlobalTheory.FlatAcycShift.dbar_coeff_transl <;> assumption)
