import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataBoundOfHalfFlip
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.data_bound_of_half_flip : GlobalTheory.FunPr.Hypotheses₂ → BigC fun _ ch C _ => FlipAt ch (C / 2) → DatAt ch C := by
  first | exact @GlobalTheory.ArchTens.Unfold.datK | exact GlobalTheory.ArchTens.Unfold.datK | (intros; apply GlobalTheory.ArchTens.Unfold.datK <;> assumption)
