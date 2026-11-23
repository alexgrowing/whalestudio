import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapPairCompat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_map_pair_compat : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ ξ : Fin n → E, form σ X.J ξ ξ ≠ 0 → ∃ κ : F, κ ≠ 0 ∧ ∀ (t : AF F) (z : UA σ W.J), z ∈ unip σ W H' →
      mat z⁻¹ *ᵥ incV F H'.y = incV F H'.y - algebraMap (AF F) (AE F E) t • incV F H'.x → ∀ (u : UA σ W.J), ∀ Ψ ∈ schA F (Fin n × Fin d),
      thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, z * u) Ψ))) = B.ψ (t * algebraMap F (AF F) κ) * thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u) Ψ))) := by
  first | exact @GlobalTheory.ThK.AnisPhase.thetaSum_center_phase | exact GlobalTheory.ThK.AnisPhase.thetaSum_center_phase | (intros; apply GlobalTheory.ThK.AnisPhase.thetaSum_center_phase <;> assumption)
