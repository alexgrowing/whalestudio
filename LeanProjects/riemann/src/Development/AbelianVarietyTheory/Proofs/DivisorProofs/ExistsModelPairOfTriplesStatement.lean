import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelPairOfTriples
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_pair_of_triples : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∃ (M₂ : Model σ G.V G₁.W) (om₂ : Rep σ G.V G₁.W),
      IsPair B M₂ X.β (X.β / X.α) om₂ (b + 2 - G.p) G.p (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) := by
  first | exact @GlobalTheory.ThK.MidPair.exists_midPair | exact GlobalTheory.ThK.MidPair.exists_midPair | (intros; apply GlobalTheory.ThK.MidPair.exists_midPair <;> assumption)
