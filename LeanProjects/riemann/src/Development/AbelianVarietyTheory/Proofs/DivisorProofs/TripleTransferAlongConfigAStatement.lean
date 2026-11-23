import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTransferAlongConfigA
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_transfer_along_config_a : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (v : Pl F) (μKv : Measure (KAt K (evFin F v)))
      (μv : Measure (idelesAt E (evFin F v))), IsNormK K (evFin F v) μKv → IsNormE E v μv →
    ∀ l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) → ℂ,
      (∀ p ∈ SB (Fin b × Fin (b + a') → Fv F v), ∀ q ∈ SB (Fin b × Fin (b + a') → Fv F v), l (p + q) = l p + l q) →
      (∀ c : ℂ, ∀ p ∈ SB (Fin b × Fin (b + a') → Fv F v), l (c • p) = c * l p) →
      (∃ p ∈ SB (Fin b × Fin (b + a') → Fv F v), l p ≠ 0) →
      (∀ g ∈ UAt σ G₁.V (evFin F v), ∀ p ∈ SB (Fin b × Fin (b + a') → Fv F v), ∀ p₁ ∈ SB (Fin b × Fin (b + a') → Fv F v),
        Acts (evFin F v) (om₁ (g, 1)) p p₁ → l p₁ = l p) →
      ∃ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μKv μv (shiftA H H') X.ν ((b + 2 - a') / 2) φ ∈ SB (Fin b × Fin (b + a') → Fv F v) ∧
        l (coneFin B G.M om v (ev v) K μKv μv (shiftA H H') X.ν ((b + 2 - a') / 2) φ) ≠ 0 := by
  first | exact @GlobalTheory.ConeBump.nonzero_coneFin | exact GlobalTheory.ConeBump.nonzero_coneFin | (intros; apply GlobalTheory.ConeBump.nonzero_coneFin <;> assumption)
