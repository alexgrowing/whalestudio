import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameLocalDeterminant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
open GlobalTheory.LineFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_local_determinant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d m r s i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E m) (H : Plane E d m), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (hA : H.IsAdapted σ B W W₁ i₀ i₁),
      ((GlobalTheory.JacGeom.frame H.x H.ι H.y).submatrix id (GlobalTheory.LineFrame.frameEquiv hA.rank).symm).det ≠ 0 → W₁.J.det ≠ 0 →
      ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (u : GL (Fin d) (Fv F v)) (X : Matrix (Fin 1) (Fin m ⊕ Fin 1) (Fv F v))
        (Y : Matrix (Fin m) (Fin 1) (Fv F v)),
        (u : Matrix (Fin d) (Fin d) (Fv F v)).submatrix (GlobalTheory.LineFrame.frameEquiv hA.rank) (GlobalTheory.LineFrame.frameEquiv hA.rank) =
          Matrix.fromBlocks 1 X 0 (Matrix.fromBlocks 1 Y 0 1) →
        ∃ g ∈ unip σ W H, g ∈ UAt σ W (evFin F v) ∧
          (mat g).map (piW t) = ((GlobalTheory.LineFrame.frameGL t H hA.rank * u * (GlobalTheory.LineFrame.frameGL t H hA.rank)⁻¹ :
            GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.LineFrame.exists_unip_frameGL | exact GlobalTheory.LineFrame.exists_unip_frameGL | (intros; apply GlobalTheory.LineFrame.exists_unip_frameGL <;> assumption)
