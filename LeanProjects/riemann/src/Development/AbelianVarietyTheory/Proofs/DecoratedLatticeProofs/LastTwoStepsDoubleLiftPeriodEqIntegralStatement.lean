import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastTwoSteps_doubleLiftPeriod_eq_integral : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → c.VolLast → t.Is → WeilOK (t := t) v → LastLaw D → SeeLast D → ∀ j (h : j + 2 * 0 + 2 = D.R.m) Φ₁ Φ₂ φ F, IsThetaFunO c.ψ _ _ Φ₁ → IsThetaFunO c.ψ _ _ Φ₂ → IsContAut (c.X j) φ → IsContAut c.T F → IsContAut (c.V j) (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.omT j h) c.volT.μ c.volT.𝓕 F Φ₂) Φ₁) ∧ ∀ g b bT, (c.B j 0 h).per c.ψ φ (rTrans g (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.omT j h) c.volT.μ c.volT.𝓕 F Φ₂) Φ₁)) = ∫ h' in c.volT.𝓕, rTrans bT F h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, b) Φ₁) (t.omT j h (b, bT) Φ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  first | exact @GlobalTheory.LastRed.main | exact GlobalTheory.LastRed.main | (intros; apply GlobalTheory.LastRed.main <;> assumption)
