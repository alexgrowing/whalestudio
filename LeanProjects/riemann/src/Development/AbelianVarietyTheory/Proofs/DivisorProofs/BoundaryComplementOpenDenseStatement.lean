import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComplementOpenDense
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_complement_open_dense : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y) (L : ReciprocityTheory.AnForm.M.LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.IsBoundary A L s W → IsOpen (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) ∧ Dense (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.opn s) := by
  first | exact @GlobalTheory.SectionZero.isOpen_and_dense_opn | exact GlobalTheory.SectionZero.isOpen_and_dense_opn | (intros; apply GlobalTheory.SectionZero.isOpen_and_dense_opn <;> assumption)
