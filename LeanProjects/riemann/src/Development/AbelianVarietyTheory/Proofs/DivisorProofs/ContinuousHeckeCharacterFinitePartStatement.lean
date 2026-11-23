import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeckeCharacterFinitePart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPhaseAt

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_heckeCharacterFinitePart : ∀ {D : D7} {N : ℕ} (c : HeckeU D N), Continuous (GlobalTheory.HeckeUChar.finChar c) := by
  first | exact @GlobalTheory.HeckeUChar.continuous_finChar | exact GlobalTheory.HeckeUChar.continuous_finChar | (intros; apply GlobalTheory.HeckeUChar.continuous_finChar <;> assumption)
