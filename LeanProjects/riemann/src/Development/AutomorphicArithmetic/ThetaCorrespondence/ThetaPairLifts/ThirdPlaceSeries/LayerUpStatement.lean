import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLatticeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUp
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z)), ∃ (nch' : NChoice (w.D (upL Z S' N h))) (xd' : ThData (w.D (upL Z S' N h))), Kept nch nch' ∧ (S' = Z.S → HEq nch' (nchTr (D := w.D Z) N h nch) ∧ HEq xd' (xdTr (D := w.D Z) N h xd)) ∧ (NchT w Z Wt nch → Nonempty (NchT w (upL Z S' N h) Wt nch')) ∧ (GoodO (w.D Z) nch xd → GoodO (w.D (upL Z S' N h)) nch' xd') ∧ ∀ (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (n : NchT w Z Wt nch) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0') (n' : NchT w (upL Z S' N h) Wt nch'), RowsSame t t' → HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) K B f T w Z Wt p0 t nch n xd → Nonempty (_root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) K B f T w (upL Z S' N h) Wt p0' t' nch' n' xd') := by
  first | exact @_root_.GlobalTheory.LayerMove.exists_kept_nChoice_thData_upL | exact _root_.GlobalTheory.LayerMove.exists_kept_nChoice_thData_upL | (intros; apply _root_.GlobalTheory.LayerMove.exists_kept_nChoice_thData_upL <;> assumption)
end
