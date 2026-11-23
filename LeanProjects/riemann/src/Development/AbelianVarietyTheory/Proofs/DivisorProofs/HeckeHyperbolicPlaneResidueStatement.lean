import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHyperbolicPlaneResidue
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.LocTypeGood
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_hyperbolic_plane_residue : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (α β : Chr F E) (v : Pl F) (τ : E →ₐ[F] Fv F v), NotRealPow τ α β →
    IsHecke F E α → IsHecke F E β → ∀ kα : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range α kα →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), n = n₁ + 2 → form σ W.J H.x H.x = 0 →
    form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
    (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
    ∀ (εW : F) (hermW : ∀ i j, σ (W.J j i) = algebraMap F E εW * W.J i j) (hJW : IsUnit (W.J.map τ).det)
      (ε₁ : F) (herm₁ : ∀ i j, σ (W₁.J j i) = algebraMap F E ε₁ * W₁.J i j) (hJ₁ : IsUnit (W₁.J.map τ).det)
      (x x' : ℕ) (eW : Fin (x + 2 + x') ≃ Fin n) (e₁ : Fin (x + x') ≃ Fin n₁) (Kh : Set (UA σ W.J))
      (S : Submodule ℂ (UA σ W.J → ℂ)),
      (∀ f ∈ S, Continuous f ∧ ∀ γ ∈ ratU σ W.J, ∀ z, f (γ * z) = f z) →
      (∀ f ∈ S, HasLocType hcm τ W.J εW hermW hJW eW (chrW α τ) (chrW β τ) f) →
      ∀ g ∈ alphaSpan W₁ H α β ((x' : ℝ) / 2) (((x + 2 : ℕ) : ℝ) / 2) Kh S,
        HasLocType hcm τ W₁.J ε₁ herm₁ hJ₁ e₁ (chrW α τ) (chrW β τ) g := by
  first | exact @GlobalTheory.LocTypeStep.hasLocType_alphaSpan | exact GlobalTheory.LocTypeStep.hasLocType_alphaSpan | (intros; apply GlobalTheory.LocTypeStep.hasLocType_alphaSpan <;> assumption)
