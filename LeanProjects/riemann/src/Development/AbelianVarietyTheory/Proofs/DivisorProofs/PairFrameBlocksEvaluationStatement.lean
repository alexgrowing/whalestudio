import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFrameBlocksEvaluation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_frame_blocks_evaluation : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∃ ex : Fin q → ℝ, ∀ (t : Fin q → ℝ) (a : UA σ X.J) (c : ℂ), (∀ i, 0 < t i) → IsTorusU x y t a →
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ z, e (om (a, 1) Ψ) z = c * e Ψ (blkScale blk t z)) →
      ‖c‖ ≤ ∏ i, t i ^ ex i := by
  first | exact @GlobalTheory.ThKTorus.ScaleBound.norm_scalar_le | exact GlobalTheory.ThKTorus.ScaleBound.norm_scalar_le | (intros; apply GlobalTheory.ThKTorus.ScaleBound.norm_scalar_le <;> assumption)
