import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleSixthForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_b_triple_sixth_form : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ (μKv : Measure (KAt K (evFin F B.v₁))) (μv : Measure (idelesAt E (evFin F B.v₁))),
    IsNormK K (evFin F B.v₁) μKv → IsNormE E B.v₁ μv →
    ∀ h ∈ UAt σ G₁.W (evFin F B.v₁), ∀ φ ∈ (Submodule.span ℂ (coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) '' G.M'.SoLoc B.ψ B.τ₁) ⊔ augAt om₁' B.v₁), ∀ φ₁ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁),
      Acts (evFin F B.v₁) (om₁' (1, h)) φ φ₁ → φ₁ ∈ (Submodule.span ℂ (coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) '' G.M'.SoLoc B.ψ B.τ₁) ⊔ augAt om₁' B.v₁) := by
  first | exact @GlobalTheory.ConeStabLv.span_cone_aug_stable | exact GlobalTheory.ConeStabLv.span_cone_aug_stable | (intros; apply GlobalTheory.ConeStabLv.span_cone_aug_stable <;> assumption)
