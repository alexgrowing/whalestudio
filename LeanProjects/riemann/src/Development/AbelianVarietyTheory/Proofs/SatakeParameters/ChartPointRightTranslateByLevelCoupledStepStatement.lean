import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoint_right_translate_by_level_coupled_step : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hj : t.m2 + 1 ≤ D.R.m) (β' : (St (t.m2 + 1) hj).Ch)
    (x' x₁' : UA D (t.m2 + 1) hj) (κ' : ((St (t.m2 + 1) hj).K β').lev.U) p', x₁'.1 = x'.1 * κ'.1 → IsPtAd A a (t.m2 + 1) hj β' x' p' →
    ∃ (q' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
      IsPtAd A a (t.m2 + 1) hj β' x₁' q' ∧
      (∀ (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) w, phiT t.X.K p.deco.1 q'.deco.1 w = phiT t.X.K p.deco.1 p'.deco.1 w) ∧
      (∀ P, frsF t.sel (t.tup μ) q' P = frsF t.sel (t.tup μ) p' P * ((κ'' P)⁻¹).1) ∧
      ∀ P, InFrame t.seam (A.fb (t.m2 + 1) hj β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) := by
  first | exact @GlobalTheory.CplPt.ptAd_levCpl | exact GlobalTheory.CplPt.ptAd_levCpl | (intros; apply GlobalTheory.CplPt.ptAd_levCpl <;> assumption)
