import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelAtBadPrimes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coupledStep_chart_level_at_bad_primes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∃ c : SB t μ → t.X.Kˣ,
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
        ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P) (c P)) ∧
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = ((((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.chi κ' : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CplLev.levAt_cpl | exact GlobalTheory.CplLev.levAt_cpl | (intros; apply GlobalTheory.CplLev.levAt_cpl <;> assumption)
