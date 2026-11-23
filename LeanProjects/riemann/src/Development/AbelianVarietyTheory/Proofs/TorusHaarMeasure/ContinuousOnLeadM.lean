import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NmatZeroMemBor
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.DivLead

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuousOn_leadM {r n δ : ℕ} (X : Data E r) {U : Set (Frame X.Ψ r)}
    {s : Fin n → Frame X.Ψ r → ℂ} {w : Frame X.Ψ r → ℂ} {t : Fin δ → Frame X.Ψ r → ℂ}
    (hs : ∀ k, ContinuousOn (s k) U) (hw : ContinuousOn w U) (ht : ∀ k, ContinuousOn (t k) U)
    (T a : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) : ContinuousOn (leadM X s w t T a cc) U := by
  unfold leadM monoM
  refine continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun k _ => ?_
  exact ((continuousOn_const.mul
    (continuousOn_finsetProd _ fun q _ => (hs q).pow _)).mul (hw.pow _)).mul (ht k)

theorem main : DivLeadStatement (E := E) := by
  intro r X Xa Fl δ t ht hb f hf
  obtain ⟨cc, hcc⟩ := GlobalTheory.LeadJets.main r X Xa Fl Xa.Fp Xa.T (Xa.T - nd X) δ (by omega) t ht hb f hf
  refine ⟨cc, GlobalTheory.vanS_of_isBigO r X Xa Fl _ _ ?_ hcc⟩
  exact hf.1.continuousOn.sub (continuousOn_leadM X
    (fun k => (Fl.s_van k).1.1.1.1.continuousOn) Fl.weightForm_vanishes.1.1.1.1.continuousOn
    (fun k => (ht k).1.continuousOn) _ _ cc)

end GlobalTheory.DivLead
