import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATriplesCompatibility
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_triples_compatibility : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (a n N : ℕ), ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), ∀ (h : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (l : (AE F E)ˣ), l ∈ idelesAt E (evI F) →
      (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N * SchwartzMap.seminorm ℂ a n (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) h)) ≤
        C * (s.sup (schwartzSeminormFamily ℂ (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ℂ)) h := by
  first | exact @GlobalTheory.ConeDecay.decay | exact GlobalTheory.ConeDecay.decay | (intros; apply GlobalTheory.ConeDecay.decay <;> assumption)
