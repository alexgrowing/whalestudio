import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBIntermediateModelEvaluation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_intermediate_model_evaluation : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (Mm : Model σ G₁.V' G.W), Mm.IsGood B.ψ →
    ∀ e₁, IsEv B G.M' Mm H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ →
    ∀ e₂, IsEv B Mm G₁.M' 1 H'.ι (iso0 b H') e₂ →
      ∃ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e₂ (e₁ Φ) ≠ 0 := by
  first | exact @GlobalTheory.ThK.EvCompNe.comp_ne_zero | exact GlobalTheory.ThK.EvCompNe.comp_ne_zero | (intros; apply GlobalTheory.ThK.EvCompNe.comp_ne_zero <;> assumption)
