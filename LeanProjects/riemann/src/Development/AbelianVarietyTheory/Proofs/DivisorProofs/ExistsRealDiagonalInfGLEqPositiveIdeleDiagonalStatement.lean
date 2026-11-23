import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧ diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  first | exact @GlobalTheory.SiegelTorusInf.exists_diag_infGL | exact GlobalTheory.SiegelTorusInf.exists_diag_infGL | (intros; apply GlobalTheory.SiegelTorusInf.exists_diag_infGL <;> assumption)
