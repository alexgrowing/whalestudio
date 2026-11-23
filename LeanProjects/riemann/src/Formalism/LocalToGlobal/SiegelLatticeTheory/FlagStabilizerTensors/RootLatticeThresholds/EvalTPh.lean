import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
import Formalism.LocalToGlobal.IndefiniteReal.ModelConjugation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.IndefiniteReal.MeasurableMulGA

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

namespace Formalism.L2.SG.EvalTPh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem phLoc_int_of_gap (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (v : NumberField.InfinitePlace X.B.I.F) :
    Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
    (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X Formalism.L2.SG.Closed.CoefWeightedLoc_holds hG) v
  have hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
    Integrable.mono' h.norm
      ((Formalism.L2.SG.WuDecayPf.continuous_coefV X v).star).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by rw [norm_star])
  have h2 := hs.const_mul ((X.dv v : ℝ) : ℂ)
  convert h2 using 1
  funext g
  rfl

variable {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} {E : Submodule ℂ (MMap M)}
  {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {v₀ : M.Vec}

end Formalism.L2.SG.EvalTPh

end
