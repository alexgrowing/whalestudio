import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseAFour
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_pair_period_identity_case_a_four : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (v : Pl F) (k : UA σ G.V.J), k ∈ UAt σ G.V (evFin F v) → ∀ l : (AE F E)ˣ, l ∈ idelesAt E (evFin F v) →
      mat k *ᵥ incV F H.x = (l : AE F E) • incV F H.x → ∃ g₁ ∈ UAt σ G₁.V (evFin F v),
      ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ k l =
          (((X.β / X.α) l : ℂ) * (((absE F E l : ℝ) ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) •
            locOp v (om₁ (g₁, 1)) (GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ 1 1) := by
  first | exact @GlobalTheory.ConeLaw.integ_law | exact GlobalTheory.ConeLaw.integ_law | (intros; apply GlobalTheory.ConeLaw.integ_law <;> assumption)
