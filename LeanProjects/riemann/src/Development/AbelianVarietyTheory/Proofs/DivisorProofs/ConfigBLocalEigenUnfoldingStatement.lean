import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenUnfolding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_local_eigen_unfolding : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ μ : Measure (idelesAt E (evI F)), μ.IsHaarMeasure → ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
      ∀ f, ContinuousOn (GlobalTheory.ThK.InfB.coneFun B G.M' om' ei' μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l f)
        (UAt σ G.V' (evI F)) := by
  first | exact @GlobalTheory.ThK.InfB.coneFun_continuousOn | exact GlobalTheory.ThK.InfB.coneFun_continuousOn | (intros; apply GlobalTheory.ThK.InfB.coneFun_continuousOn <;> assumption)
