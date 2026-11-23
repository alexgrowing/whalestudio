import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameTorusLatticeAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_torus_lattice_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (q : ℕ) (x y : Fin q → Fin n → E) (M₁ : Model σ X W)
    (blk : Fin q → Finset (Fin n × Fin d)), M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk →
    (∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a) →
    ∀ (i : Fin q) (z : Fin d → AE F E), ∃ z' : Fin n × Fin d → AF F, (∀ j, j ∉ blk i → z' j = 0) ∧
      M₁.co.e (Matrix.vecMulVec (incV F (x i)) z) = (0, z') := by
  first | exact @GlobalTheory.ThKTorus.frameCo_vecMulVec_mem_block | exact GlobalTheory.ThKTorus.frameCo_vecMulVec_mem_block | (intros; apply GlobalTheory.ThKTorus.frameCo_vecMulVec_mem_block <;> assumption)
