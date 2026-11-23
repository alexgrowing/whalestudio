import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedTensorRepresentative
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_restricted_tensor_representative : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) (h : UA σ G.W.J),
      (∀ w, φ w ∈ SB _) → (∀ᶠ w in cofinite, φ w = G.M.vac w) →
      ∃ l : SInf F (Fin a × Fin (a + a')) →L[ℂ] ℂ, (∀ f, l f = G.M.I om (pure f φ) h) ∧
        ∀ g ∈ UAt σ G.V (evI F), ∀ f f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, 1)) f f₁ → l f₁ = l f := by
  first | exact @GlobalTheory.ThKFunInf.funInf | exact GlobalTheory.ThKFunInf.funInf | (intros; apply GlobalTheory.ThKFunInf.funInf <;> assumption)
