import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AutomorphicArithmetic.DivisorFrames.ThetaPairPlaneCompat
import Development.AutomorphicArithmetic.DivisorFrames.ExistsUnipotentHeisenberg
import Development.AutomorphicArithmetic.DivisorFrames.ThetaPairPlaneIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

private theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {U : Type} [AddCommGroup U] [Module R U]
    {B : U → U → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ)
    (Φ : (κ → R) → ℂ) : co.rho ψ 0 Φ = Φ := by
  funext z
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

private theorem form_self_skew {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (ξ : Fin n → E) : σ (form σ J ξ ξ) = -form σ J ξ ξ := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

private theorem invOf_two_eq' {F : Type} [Field F] [NumberField F] : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  apply invOf_eq_right_inv
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  norm_num

theorem UpperTheory.pair_restriction_compatible_with_models :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
                 (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (M : Model σ X W) (M₂ : Model σ X₁ W) (H : Plane E n n₁) (j₀ j₁ : ℕ)
                 (χX χW : Chr F E) (om : Rep σ X W) (om₂ : Rep σ X₁ W) (r s r₁ s₁ r' s' : ℕ),
                 IsPair B M χX χW om r s r' s' → IsPair B M₂ χX χW om₂ r₁ s₁ r' s' → H.IsAdapted σ B X X₁ j₀ j₁ →
                 ∀ e₁ : Fn F n d →ₗ[ℂ] Fn F n₁ d, IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ →
                 ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
                   IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 → ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ w : Fin d → E,
                   form σ W.J w w ≠ 0 → ∫ u in 𝓕, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) ∂μ = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he μ 𝓕 hμ h𝓕 h1 Ψ hΨ w hw
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.AdelicU.cm_conj_conj hP.base.cm
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hP.base.cm
  set f : E := δ * form σ W.J w w with hf
  have hf0 : f ≠ 0 := mul_ne_zero hδ hw
  have hσf : σ f = f := by
    rw [hf, map_mul, hσδ, form_self_skew hσ hP.skew.skew w, neg_mul_neg]
  have htr : Algebra.trace F E f ≠ 0 := by
    intro h0
    have h1 := GlobalTheory.SplitAdeleTrace.add_conj_eq_trace hP.base.cm f
    rw [hσf, h0, map_zero, ← two_mul] at h1
    exact hf0 ((mul_eq_zero.1 h1).resolve_left two_ne_zero)
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.T.standard_adelic_char_exists_ne_one F B.ψ hP.base.std
  set t : AF F := s₀ * algebraMap F (AF F) (2 / Algebra.trace F E f) with ht
  set β : AE F E := t ⊗ₜ[F] δ with hβ
  have hβ' : β = algebraMap (AF F) (AE F E) t * inclR (F := F) (AF F) δ := by
    rw [hβ, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show _ = (t ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] δ)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hβc : β + cA σ β = -GlobalTheory.UnipMass.hA σ X₁.J 0 0 := by
    rw [GlobalTheory.UnipMass.hA_zero_left, hβ', map_mul (cA σ), AlgHom.commutes, GlobalTheory.UnipMass.cA_inclR, hσδ, map_neg]
    ring
  obtain ⟨g, hgU, hgy, hgc⟩ := UpperTheory.exists_unipotent_heisenberg F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hP.base hP.herm hP₂.herm hH 0 β hβc
  have hph : ⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (β * GlobalTheory.UnipMass.hA σ W.J (incV F w) (incV F w)) = s₀ := by
    have e3 : β * GlobalTheory.UnipMass.hA σ W.J (incV F w) (incV F w) = t ⊗ₜ[F] f := by
      rw [GlobalTheory.UnipMass.hA_incV, hβ]
      show (t ⊗ₜ[F] δ) * ((1 : AF F) ⊗ₜ[F] form σ W.J w w) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [e3, GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul, invOf_two_eq', ht, mul_assoc, ← map_mul,
      div_mul_cancel₀ _ htr, mul_left_comm, ← map_mul]
    norm_num
  have hsplit := IsUWeilPair.isUSplitting hP.weil
  refine GlobalTheory.IsoPhase.setIntegral_eq_zero_of_mul_right σ X H μ 𝓕 h𝓕 h1
    (fun u => thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))))
    (fun γ hγ x => UpperTheory.theta_pair_plane_integral hKP F E σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he
      w γ.1 (Subgroup.mem_subgroupOf.1 hγ) γ.2 x.1 Ψ hΨ) ⟨g, hgU⟩ (B.ψ s₀) hs₀ fun x => ?_
  have hΦ : om (x.1, 1) Ψ ∈ schA F (Fin n × Fin d) := hsplit.pres (x.1, 1) Ψ hΨ
  have hmul : om (x.1 * g, 1) Ψ = om (g, 1) (om (x.1, 1) Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, hgc rfl _ x.2]
  have hm := UpperTheory.theta_pair_plane_compat hKP F E σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he
    g hgU 0 β hgy (incV F w) _ hΦ
  rw [hph, Matrix.zero_vecMulVec, rho_zero'] at hm
  show thetaSum F (e₁ (M.co.rho B.ψ _ (om (x.1 * g, 1) Ψ))) = _
  rw [hmul, hm]
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left
