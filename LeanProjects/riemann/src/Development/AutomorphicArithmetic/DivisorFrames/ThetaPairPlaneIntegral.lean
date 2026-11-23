import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AutomorphicArithmetic.DivisorFrames.ThetaPairPlaneCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormSmulLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapPairCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

theorem UpperTheory.theta_pair_plane_integral :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
                 (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (M : Model σ X W) (M₂ : Model σ X₁ W) (H : Plane E n n₁) (j₀ j₁ : ℕ)
                 (χX χW : Chr F E) (om : Rep σ X W) (om₂ : Rep σ X₁ W) (r s r₁ s₁ r' s' : ℕ),
                 IsPair B M χX χW om r s r' s' → IsPair B M₂ χX χW om₂ r₁ s₁ r' s' → H.IsAdapted σ B X X₁ j₀ j₁ →
                 ∀ e₁ : Fn F n d →ₗ[ℂ] Fn F n₁ d, IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ →
                 ∀ (w : Fin d → E), ∀ γ ∈ ratU σ X.J, γ ∈ unip σ X H → ∀ (u : UA σ X.J), ∀ Ψ ∈ schA F (Fin n × Fin d),
                   thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (γ * u, 1) Ψ))) = thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he w γ hγr hγu u Ψ hΨ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hP.base.cm.2.2.1]; norm_num)
  have hψ : IsStd B.ψ := hP.base.std
  have hspl := IsUWeilPair.isUSplitting hP.weil
  have hΦ : om (u, 1) Ψ ∈ schA F (Fin n × Fin d) := hspl.pres (u, 1) Ψ hΨ
  obtain ⟨G, hG⟩ := GlobalTheory.AnisRatInv.exists_rat (inv_mem hγr)
  have hGu : Gᵀ * X.J * G.map σ = X.J := GlobalTheory.AnisRatInv.unitary_rat _ G hG
  have hGx : G *ᵥ H.x = H.x := GlobalTheory.AnisRatInv.incV_injective (F := F) (by
    rw [← GlobalTheory.UnipLine.incM_mulVec_incV, ← hG]; exact GlobalTheory.AnisRatInv.unip_fix (inv_mem hγu))
  obtain ⟨a, t, b, hv⟩ := GlobalTheory.UnipLine.span_E hH hP.herm (G *ᵥ H.y - H.y)
  have hyx : form σ X.J H.y H.x ≠ 0 := GlobalTheory.UnipLine.form_y_x_ne hH hP.herm
  have ht : t = 0 := by
    have h0 : form σ X.J (G *ᵥ H.y - H.y) H.x = 0 := by
      rw [GlobalTheory.AnisRatInv.form_sub_left]
      conv_lhs => rw [← hGx]
      rw [GlobalTheory.AnisRatInv.form_mulVec σ X.J G hGu, hGx, sub_self]
    rw [hv, GlobalTheory.AnisRatInv.form_add_left, GlobalTheory.AnisRatInv.form_add_left, GlobalTheory.AnisRatInv.form_smul_left,
      GlobalTheory.AnisRatInv.form_smul_left, hH.xx, (hH.orth b).1, mul_zero, zero_add, zero_add] at h0
    exact (mul_eq_zero.1 h0).resolve_right hyx
  subst ht
  have hGy : G *ᵥ H.y = H.y + H.ι *ᵥ b + a • H.x := by
    rw [zero_smul, add_zero, sub_eq_iff_eq_add'] at hv
    rw [hv]; abel
  have hy : mat γ⁻¹ *ᵥ incV F H.y =
      incV F H.y + incM F H.ι *ᵥ incV F b + inclR (F := F) (AF F) a • incV F H.x := by
    rw [hG, GlobalTheory.UnipLine.incM_mulVec_incV, GlobalTheory.UnipLine.incM_mulVec_incV, hGy]
    funext i
    simp only [incV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  have hmul : om (γ * u, 1) Ψ = om (γ, 1) (om (u, 1) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hph : B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E)
      (inclR (F := F) (AF F) a * GlobalTheory.UnipMass.hA σ W.J (incV F w) (incV F w))) = 1 := by
    rw [GlobalTheory.UnipMass.hA_incV, ← map_mul,
      show inclR (F := F) (AF F) (a * form σ W.J w w) = (1 : AF F) ⊗ₜ[F] (a * form σ W.J w w) from rfl,
      GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul, one_mul, GlobalTheory.ThK.AnisPhase.invOf_two_eq, ← map_mul]
    exact hψ.2.1 _
  rw [hmul, UpperTheory.theta_pair_plane_compat hKP F E σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he γ hγu
    (incV F b) (inclR (F := F) (AF F) a) hy (incV F w) _ hΦ, hph, one_smul, ← GlobalTheory.ThetaExpandInv.incM_vecMulVec b w,
    GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₂ hψ hP₂.good]
