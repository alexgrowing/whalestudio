import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTransferAlongConfigAThird
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_transfer_along_config_a_third : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μKi : Measure (KAt K (evI F))) (μi : Measure (idelesAt E (evI F))) (μKf : ∀ v : Pl F, Measure (KAt K (evFin F v)))
      (μf : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), IsNormK K (evI F) μKi → μi.IsHaarMeasure →
      (∀ v, IsNormK K (evFin F v) (μKf v)) → (∀ v, IsNormE E v (μf v)) → ∀ T : Finset (Pl F), X.T ⊆ T →
    ∀ (f₁ : SInf F (Fin b × Fin (b + a'))) (φ₁ : ∀ v : Pl F, (Fin b × Fin (b + a') → Fv F v) → ℂ) (h₁ : UA σ G₁.W.J),
      (∀ v, φ₁ v ∈ SB _) → (∀ v ∉ T, φ₁ v = G₁.M.vac v) → G₁.M.I om₁ (pure f₁ φ₁) h₁ ≠ 0 →
      ∃ f ∈ G.M.Pol B.ψ B.emb, ∃ φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ,
        (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = G.M.vac v) ∧
        G₁.M.I om₁ (pure (coneInf B G.M om ei K μKi μi (shiftA H H') X.ν ((b + 2 - a') / 2) f) (fun v => if v ∈ T then coneFin B G.M om v (ev v) K (μKf v) (μf v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) else G₁.M.vac v)) h₁ ≠ 0 := by
  first | exact @GlobalTheory.ThK.exists_local_data_cone_ne_zero | exact GlobalTheory.ThK.exists_local_data_cone_ne_zero | (intros; apply GlobalTheory.ThK.exists_local_data_cone_ne_zero <;> assumption)
