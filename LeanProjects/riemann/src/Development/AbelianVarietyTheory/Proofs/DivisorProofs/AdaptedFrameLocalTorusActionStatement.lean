import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameLocalTorusAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
open GlobalTheory.LineFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_local_torus_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d m i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E m) (H : Plane E d m) (hcm : IsCMExt F E σ)
    (hA : H.IsAdapted σ B W W₁ i₀ i₁),
      ((GlobalTheory.JacGeom.frame H.x H.ι H.y).submatrix id (GlobalTheory.LineFrame.frameEquiv hA.rank).symm).det ≠ 0 →
      ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (h2 : 2 ≤ d) (y : (Fv F v)ˣ) (g : UA σ W.J),
        IsLevi (W₁ := W₁) H (GlobalTheory.JacGeom.idl hcm t (y, 1)) 1 g →
        (mat g).map (piW t) = ((GlobalTheory.LineFrame.frameGL t H hA.rank * leviEmb (Fv F v) (linePlace h2) (firstBlockScalar (Fv F v) d y) *
          (GlobalTheory.LineFrame.frameGL t H hA.rank)⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.LeviFrameSplit.levi_frame_conj | exact GlobalTheory.LeviFrameSplit.levi_frame_conj | (intros; apply GlobalTheory.LeviFrameSplit.levi_frame_conj <;> assumption)
