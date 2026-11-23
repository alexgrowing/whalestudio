import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartzFunction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_tensor_schwartz_function : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ)
      (h : UA σ G.W.J) (v : Pl F), (∀ w, φ w ∈ SB _) → (∀ᶠ w in cofinite, φ w = G.M.vac w) →
      (∀ p ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ q ∈ SB (Fin a × Fin (a + a') → Fv F v),
        G.M.I om (pure f (Function.update φ v (p + q))) h =
          G.M.I om (pure f (Function.update φ v p)) h + G.M.I om (pure f (Function.update φ v q)) h) ∧
      (∀ c : ℂ, ∀ p ∈ SB (Fin a × Fin (a + a') → Fv F v),
        G.M.I om (pure f (Function.update φ v (c • p))) h = c * G.M.I om (pure f (Function.update φ v p)) h) ∧
      ∀ g ∈ UAt σ G.V (evFin F v), ∀ p ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ p₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (g, 1)) p p₁ →
        G.M.I om (pure f (Function.update φ v p₁)) h = G.M.I om (pure f (Function.update φ v p)) h := by
  first | exact @GlobalTheory.ThK.FunFin.thetaIntegral_fin | exact GlobalTheory.ThK.FunFin.thetaIntegral_fin | (intros; apply GlobalTheory.ThK.FunFin.thetaIntegral_fin <;> assumption)
