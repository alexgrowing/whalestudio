import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilMeasureOfCongruentForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_place_lies_over : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ → LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  first | (exact @GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver) | (exact GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver) | (intros; apply GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver  <;> assumption)
