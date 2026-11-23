import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTriple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_local_eigen_triple : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evI F) → ∀ f, ei' (locOpInf (om' (u, 1)) f) = ei' f) ∧
      ∀ t g₀ g, IsLevi H t g₀ g → g ∈ UAt σ G.V' (evI F) → g₀ ∈ UAt σ G₁.V' (evI F) → ∀ f,
        ei' (locOpInf (om' (g, 1)) f) = fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • locOpInf (om₁' (g₀, 1)) (ei' f) := by
  first | exact @GlobalTheory.ThK.EvLawBLeft.infLaw | exact GlobalTheory.ThK.EvLawBLeft.infLaw | (intros; apply GlobalTheory.ThK.EvLawBLeft.infLaw <;> assumption)
