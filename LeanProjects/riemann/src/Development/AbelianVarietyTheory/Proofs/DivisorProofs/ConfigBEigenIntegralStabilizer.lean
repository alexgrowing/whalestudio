import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerHaarIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.ConeSmall.coneI_levi : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h₁ m, IsLevi H' 1 h₁ m → ∀ h,
        GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (((a - (b + 2)) / 2 + 1 : ℕ) : ℂ) (m * h) =
          G₁.M'.I om₁' (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ')) h₁ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h₁ m hL h
  have hΦs : Φ' ∈ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΦ').2
  have hW := IsUWeilPair.isUSplitting hT.weil'
  rw [GlobalTheory.T.config_b_stabilizer_haar_integral hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁]
  unfold GlobalTheory.ConeSmall.coneI
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only [Complex.cpow_natCast]
  congr 2
  have hΨ : om' (k.1, h) Φ' ∈ schA F _ := hW.pres _ _ hΦs
  have e1 : om' (k.1, m * h) Φ' = om' (1, m) (om' (k.1, h) Φ') := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hact : actAB (cA σ) ((1, m) : UA σ G.V'.J × UA σ G.W.J) (shiftB σ H H' l) = shiftB σ H H' l := by
    have hx : mat m *ᵥ incV F H'.x = incV F H'.x := by simpa using hL.1
    ext i j
    simp only [actAB, shiftB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_apply]
    congr 1
    conv_rhs => rw [← hx]
    simp [mat, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (1, m) (om' (k.1, h) Φ')) =
      om' (1, m) (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) := by
    rw [hW.impl (1, m) (shiftB σ H H' l) _ hΨ, hact]
  have hρ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' l) _ hΨ
  rw [e1, e2, GlobalTheory.T.config_b_levi_evaluation_compatible hKP.base F E σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁ h₁ m hL _ hρ]
  simp only [Model.I, theta]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [← Module.End.mul_apply, ← map_mul]
  simp
