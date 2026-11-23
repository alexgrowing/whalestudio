import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoACoCMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_coordinate_additive_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ n₁ ∈ unip σ G.V H, ∀ n₂ ∈ unip σ G.V H,
    GlobalTheory.ThK.UnipDom.coA σ G.V.J H (n₁ * n₂) = GlobalTheory.ThK.UnipDom.coA σ G.V.J H n₁ + GlobalTheory.ThK.UnipDom.coA σ G.V.J H n₂ ∧
    GlobalTheory.ThK.UnipDom.coC σ G.V.J H (n₁ * n₂) = GlobalTheory.ThK.UnipDom.coC σ G.V.J H n₁ + GlobalTheory.ThK.UnipDom.coC σ G.V.J H n₂ +
      GlobalTheory.ThK.UnipDom.coA σ G.V.J H n₁ ⬝ᵥ GlobalTheory.UnipConj.betaOf σ G₁.V.J (GlobalTheory.ThK.UnipDom.coA σ G.V.J H n₂) := by
  first | exact @GlobalTheory.UnipConj.MulLaw.coA_coC_mul | exact GlobalTheory.UnipConj.MulLaw.coA_coC_mul | (intros; apply GlobalTheory.UnipConj.MulLaw.coA_coC_mul <;> assumption)
