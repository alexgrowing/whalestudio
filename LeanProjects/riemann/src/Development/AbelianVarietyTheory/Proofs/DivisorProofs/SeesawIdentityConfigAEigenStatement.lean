import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigAEigen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_identity_config_a_eigen : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')),
    CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (M₂ : Model σ G.V G₁.W) (om₂ : Rep σ G.V G₁.W),
      IsPair B M₂ X.β (X.β / X.α) om₂ (b + 2 - G.p) G.p (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) →
    ∀ (e₁ : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F (b + 2) (b + a')) (e₂ : Fn F (b + 2) (b + a') →ₗ[ℂ] Fn F b (b + a')),
      IsEv B G.M M₂ 1 H'.ι (iso0 (b + 2) H') e₁ → IsEv B M₂ G₁.M H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₂ →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e Ψ = c • e₂ (e₁ Ψ) := by
  first | exact @GlobalTheory.ThK.EvFactor.evA_eq_smul_comp | exact GlobalTheory.ThK.EvFactor.evA_eq_smul_comp | (intros; apply GlobalTheory.ThK.EvFactor.evA_eq_smul_comp <;> assumption)
