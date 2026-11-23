import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviTorusEvaluationStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallUnip

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem unip_fix {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) :
    ∀ u ∈ unip σ W H', mat u *ᵥ incV F H'.x = incV F H'.x := by
  intro u hu
  let S : Subgroup (UA σ W.J) :=
    { carrier := {g | mat g *ᵥ incV F H'.x = incV F H'.x}
      one_mem' := by simp [mat]
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        show ((a * b : UA σ W.J).1.1) *ᵥ _ = _
        simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
        exact (congrArg _ hb).trans ha
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        have h1 : mat a⁻¹ * mat a = 1 := by
          show ((a⁻¹ * a : UA σ W.J).1.1) = 1
          simp
        calc mat a⁻¹ *ᵥ incV F H'.x = mat a⁻¹ *ᵥ (mat a *ᵥ incV F H'.x) := by rw [ha]
          _ = incV F H'.x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] }
  have hle : unip σ W H' ≤ S := Subgroup.closure_le _ |>.2 fun g hg => hg.1
  exact hle hu

end GlobalTheory.ConeSmallUnip

theorem GlobalTheory.ConeSmall.coneI_unip : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (z : ℂ) (u : UA σ G.W.J), u ∈ unip σ G.W H' → ∀ h : UA σ G.W.J,
      GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z (u * h) = GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z h := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' z u hu h
  have hΦs : Φ' ∈ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' B.τ₁ (Submodule.mem_inf.1 hΦ').2
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hx : mat u *ᵥ incV F H'.x = incV F H'.x := GlobalTheory.ConeSmallUnip.unip_fix H' u hu
  have hLev : IsLevi (W₁ := G₁.W) H' 1 1 (1 : UA σ G.W.J) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [mat]
  unfold GlobalTheory.ConeSmall.coneI
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  have hΨ : om' (k.1, h) Φ' ∈ schA F _ := hW.pres _ _ hΦs
  have e1 : om' (k.1, u * h) Φ' = om' (1, u) (om' (k.1, h) Φ') := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hact : actAB (cA σ) ((1, u) : UA σ G.V'.J × UA σ G.W.J) (shiftB σ H H' l) = shiftB σ H H' l := by
    ext i j
    simp only [actAB, shiftB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_apply]
    congr 1
    conv_rhs => rw [← hx]
    simp [mat, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (1, u) (om' (k.1, h) Φ')) =
      om' (1, u) (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) := by
    rw [hW.impl (1, u) (shiftB σ H H' l) _ hΨ, hact]
  have hρ := GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std (shiftB σ H H' l) _ hΨ
  have e3 := GlobalTheory.T.config_b_levi_torus_evaluation hKP.base F E σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁ 1 1 1 hLev u hu _ hρ
  rw [mul_one] at e3
  dsimp only
  rw [e1, e2, e3]
  have hone : ((1 : UA σ G₁.V'.J), (1 : UA σ G₁.W.J)) = 1 := rfl
  rw [hone]
  simp
