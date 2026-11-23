import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameDetNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
open GlobalTheory.LineFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d m r s i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E m) (H : Plane E d m), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (hA : H.IsAdapted σ B W W₁ i₀ i₁),
      ((GlobalTheory.JacGeom.frame H.x H.ι H.y).submatrix id (GlobalTheory.LineFrame.frameEquiv hA.rank).symm).det ≠ 0 ∧ W₁.J.det ≠ 0 := by
  first | exact @GlobalTheory.LineFrame.frame_det_ne_zero | exact GlobalTheory.LineFrame.frame_det_ne_zero | (intros; apply GlobalTheory.LineFrame.frame_det_ne_zero <;> assumption)
