import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTriples
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_local_eigen_triples : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ μ : Measure (idelesAt E (evI F)), μ.IsHaarMeasure → ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evI F), ∀ f, l (locOpInf (om₁' (g₀, 1)) f) = l f) →
      ∀ f, ∀ p ∈ UAt σ G.V' (evI F), ∀ g ∈ UAt σ G.V' (evI F), ∀ t : (AE F E)ˣ,
        mat p *ᵥ incV F H.x = t.1 • incV F H.x →
        GlobalTheory.ThK.InfB.coneFun B G.M' om' ei' μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l f (p * g) =
          (((absE F E t : ℝ) ^ (b + 1) : ℝ) : ℂ) *
            GlobalTheory.ThK.InfB.coneFun B G.M' om' ei' μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l f g := by
  first | exact @GlobalTheory.ThK.InfB.coneFun_mul_left | exact GlobalTheory.ThK.InfB.coneFun_mul_left | (intros; apply GlobalTheory.ThK.InfB.coneFun_mul_left <;> assumption)
