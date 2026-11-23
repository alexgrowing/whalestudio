import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCocycleZeroOfGenerators
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_cocycle_zero_of_generators : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (D : Fl g → Pt E g → ℂ), (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, D (l + l') P = D l (transl τ l' P) + D l' P) → (∀ i : Fin g ⊕ Fin g, ∀ P ∈ cov U g, D (Pi.single i (1 : ℝ)) P = 0) → ∀ l ∈ stdLat g, ∀ P ∈ cov U g, D l P = 0 := by
  first | exact @GlobalTheory.cocycle_vanish_stdLat | exact GlobalTheory.cocycle_vanish_stdLat | (intros; apply GlobalTheory.cocycle_vanish_stdLat <;> assumption)
