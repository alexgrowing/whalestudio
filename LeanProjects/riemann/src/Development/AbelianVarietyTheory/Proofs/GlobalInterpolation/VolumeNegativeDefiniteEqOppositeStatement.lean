import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeNegativeDefiniteEqOpposite
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_negativeDefinite_eq_opposite : ∀ D : D7, VolTie D → ∀ (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) → D.vol W = D.vol (GlobalTheory.NegSpace.neg W) := by
  first | exact @GlobalTheory.NegVol.vol_neg_eq | exact GlobalTheory.NegVol.vol_neg_eq | (intros; apply GlobalTheory.NegVol.vol_neg_eq <;> assumption)
