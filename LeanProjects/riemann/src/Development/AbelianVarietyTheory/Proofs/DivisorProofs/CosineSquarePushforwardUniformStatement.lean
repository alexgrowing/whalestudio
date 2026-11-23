import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineSquarePushforwardUniform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosine_square_pushforward_uniform : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool), G.PosDef →
    Measure.map (GlobalTheory.LineCos.cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (GlobalTheory.LineCos.hform G (GlobalTheory.LineCos.lineVec s x) (GlobalTheory.LineCos.lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.LineCos.FsLaw.map_cosSq_fs | exact GlobalTheory.LineCos.FsLaw.map_cosSq_fs | (intros; apply GlobalTheory.LineCos.FsLaw.map_cosSq_fs <;> assumption)
