import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelEvaluation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_frame_model_evaluation : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Φ ∈ M.So B.ψ B.τ₁, ∀ (g : UA σ X.J) (h : UA σ W.J) (ξ : Fin n × Fin d → F), (∃ i, ∀ j ∈ blk i, ξ j = 0) →
      e (om (g, h) Φ) (fun j => algebraMap F (AF F) (ξ j)) = 0 := by
  first | exact @GlobalTheory.ThKTorus.vanish_of_block_zero | exact GlobalTheory.ThKTorus.vanish_of_block_zero | (intros; apply GlobalTheory.ThKTorus.vanish_of_block_zero <;> assumption)
