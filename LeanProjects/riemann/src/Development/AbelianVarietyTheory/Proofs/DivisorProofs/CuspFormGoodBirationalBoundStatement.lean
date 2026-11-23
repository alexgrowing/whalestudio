import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGoodBirationalBound
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_good_birational_bound : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (abelian₂ t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) w abelian₂ → Real.log abelian₂ ≤ t → volL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict 8 Z (wtOf (T.Q.Dw j) u 0) t ≤ ENNReal.ofReal (Y.dg u Z * (Y.ht u Z + t)) := by
  first | exact @GlobalTheory.CovHt.VolUp.volL_le | exact GlobalTheory.CovHt.VolUp.volL_le | (intros; apply GlobalTheory.CovHt.VolUp.volL_le <;> assumption)
