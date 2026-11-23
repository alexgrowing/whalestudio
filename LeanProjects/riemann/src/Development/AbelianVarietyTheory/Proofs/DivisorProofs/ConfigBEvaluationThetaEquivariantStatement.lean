import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEvaluationThetaEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_evaluation_theta_equivariant : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (μK₁ : Measure (KAt K (evFin F B.v₁))) (μ₁ : Measure (idelesAt E (evFin F B.v₁))),
    IsNormK K (evFin F B.v₁) μK₁ → IsNormE E B.v₁ μ₁ →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
    ∃ V : Submodule ℂ ((Fin b × Fin (a + b) → Fv F B.v₁) → ℂ), FiniteDimensional ℂ V ∧ V ≤ SB _ ∧
      (∀ (k : KAt K (evFin F B.v₁)) (l : idelesAt E (evFin F B.v₁)),
        (fun y => coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y) ∈ V) ∧
      ∀ y, (∀ k : KAt K (evFin F B.v₁), Integrable (fun l : idelesAt E (evFin F B.v₁) =>
          coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y) μ₁) ∧
        Integrable (fun k : KAt K (evFin F B.v₁) => ∫ l : idelesAt E (evFin F B.v₁),
          coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y ∂μ₁) μK₁ := by
  first | exact @GlobalTheory.ConeSoB.integrands_findim | exact GlobalTheory.ConeSoB.integrands_findim | (intros; apply GlobalTheory.ConeSoB.integrands_findim <;> assumption)
