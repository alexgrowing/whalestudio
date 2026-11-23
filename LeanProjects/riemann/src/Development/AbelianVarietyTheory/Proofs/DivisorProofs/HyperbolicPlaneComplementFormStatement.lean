import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_complement_form : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), (∀ x, σ (σ x) = x) →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∃ M : UA σ Y₁.J → UA σ Y.J, Continuous M ∧ (∀ h₁, IsLevi (W₁ := Y₁) H 1 h₁ (M h₁)) ∧
      ∀ γ ∈ ratU σ Y₁.J, M γ ∈ ratU σ Y.J := by
  first | exact @GlobalTheory.LeviPlaneSection.leviSection | exact GlobalTheory.LeviPlaneSection.leviSection | (intros; apply GlobalTheory.LeviPlaneSection.leviSection <;> assumption)
