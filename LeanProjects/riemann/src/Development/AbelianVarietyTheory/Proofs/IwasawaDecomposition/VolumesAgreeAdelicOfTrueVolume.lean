import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolumeStatement

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volTieG_of_trueVol : ∀ D : D7, letI := D.host.cmStar;
    (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  intro D
  letI := D.host.cmStar
  intro h
  rw [volTieG_iff]
  intro W hW
  rw [h W]
  exact GlobalTheory.T.unitaryAdelicQuotientVolume_is_volume _ _ D.sp.cm _ _ D.cd W (isCMFam_host _ D.host _ D.eTau) hW

end GlobalTheory.Mem.Vol
