import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfResidueSpanEqTop
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top : ∀ {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ} (ρ : Γ →* GL (Fin r) A), Submodule.span (IsLocalRing.ResidueField A) (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤ → Submodule.span A (Set.range (mat ρ)) = ⊤ := by
  first | exact @GlobalTheory.span_mat_eq_top_of_residue | exact GlobalTheory.span_mat_eq_top_of_residue | (intros; apply GlobalTheory.span_mat_eq_top_of_residue <;> assumption)
