import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairHypPlaneSplit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_hyp_plane_split : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (n₁ : ℕ) (H : Plane E n n₁), (n₁ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
          (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (X₁ : Spc F E n₁) (M₁ : Model σ X₁ W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d), X₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ →
      IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ Ψ ∈ schA F (Fin n × Fin d), Continuous (fun h : UA σ W.J => thetaSum F (e (om (1, h) Ψ))) ∧
        (∀ γ ∈ ratU σ W.J, ∀ h, thetaSum F (e (om (1, γ * h) Ψ)) = thetaSum F (e (om (1, h) Ψ))) ∧
        ∃ (C : ℝ) (k : ℕ), ∀ h, ‖thetaSum F (e (om (1, h) Ψ))‖ ≤ C * (ht h : ℝ) ^ k := by
  first | exact @GlobalTheory.ThKEvKernel.kernel_basic | exact GlobalTheory.ThKEvKernel.kernel_basic | (intros; apply GlobalTheory.ThKEvKernel.kernel_basic <;> assumption)
