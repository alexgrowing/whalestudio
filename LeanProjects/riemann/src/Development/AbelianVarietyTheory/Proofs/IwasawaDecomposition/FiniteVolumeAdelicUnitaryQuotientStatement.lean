import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteVolume_adelicUnitaryQuotient : FiniteVolume₂ := by
  first | exact @GlobalTheory.Mem.VolFin.finVol | exact GlobalTheory.Mem.VolFin.finVol | (intros; apply GlobalTheory.Mem.VolFin.finVol <;> assumption)
