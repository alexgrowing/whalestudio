import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianPlaneUnipotentIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_plane_unipotent_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), n = n₁ + 2 → form σ W.J H.x H.x = 0 →
    form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
    (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
    ∀ ε : F, (∀ i j, σ (W.J j i) = algebraMap F E ε * W.J i j) → W.J.det ≠ 0 → W₁.J.det ≠ 0 →
    ∃ K : Set (unip σ W H), IsCompact K ∧ ∀ u : unip σ W H, ∃ γ ∈ (ratU σ W.J).subgroupOf (unip σ W H), γ * u ∈ K := by
  first | exact @GlobalTheory.UnipCocptHerm.cocompact_unip_eps | exact GlobalTheory.UnipCocptHerm.cocompact_unip_eps | (intros; apply GlobalTheory.UnipCocptHerm.cocompact_unip_eps <;> assumption)
