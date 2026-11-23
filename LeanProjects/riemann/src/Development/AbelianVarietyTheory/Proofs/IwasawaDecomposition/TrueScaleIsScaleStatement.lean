import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cdScaleIs_trueScale' : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) := by
  first | exact @GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale | exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale | (intros; apply GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale <;> assumption)
