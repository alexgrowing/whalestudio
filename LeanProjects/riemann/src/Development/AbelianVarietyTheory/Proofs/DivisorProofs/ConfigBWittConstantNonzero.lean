import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationCompatibleLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationSeesaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseRationalValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousFunctionalLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelIntertwinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEtaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarFundamentalDomainUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEvaluationCompatibleStatement
import Development.AutomorphicArithmetic.DivisorFrames.SkewFormHermitianTwist
import Development.AutomorphicArithmetic.DivisorFrames.ExistsWittPartner
import Development.AutomorphicArithmetic.DivisorFrames.UnipotentCompactFundamentalDomain
import Development.AutomorphicArithmetic.DivisorFrames.ThetaCountableFunctionalBound
import Development.AutomorphicArithmetic.DivisorFrames.ThetaPairPlaneIntegral
import Development.AutomorphicArithmetic.DivisorFrames.ThetaPairPlaneUnipotent
import Development.AutomorphicArithmetic.DivisorFrames.UnipotentPhaseNontrivial
import Development.AutomorphicArithmetic.DivisorFrames.PairRestrictsAlongAdaptedPlane
import Development.AutomorphicArithmetic.DivisorFrames.PairRestrictionCompatibleWithModels
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeSmallUnf.CTerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M : Model σ X W} {M₂ : Model σ X₁ W}
  {M₃ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {j₀ j₁ i₀ i₁ : ℕ} {χX χW : Chr F E} {om : Rep σ X W}
  {om₂ : Rep σ X₁ W} {r s r₁ s₁ r' s' : ℕ} {e₁ : Fn F n d →ₗ[ℂ] Fn F n₁ d} {e₀ : Fn F n₁ d →ₗ[ℂ] Fn F n₁ d₁}

private local instance borelUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

private theorem expandX (hKP : KP) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hM₂ : M₂.IsGood B.ψ) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (he : IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁) :
    ∃ C : ℂ, C ≠ 0 ∧ (∃ Ψ ∈ schA F (Fin n × Fin d), thetaSum F Ψ ≠ 0) ∧ ∀ Ψ ∈ schA F (Fin n × Fin d),
      thetaSum F Ψ = C * ∑' w : Fin d → E, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ)) := by
  have hXW : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s' := ⟨r, s, r', s', hX, hW⟩
  have hl := GlobalTheory.T.adapted_mixed_model_intertwines hKP F E σ B n d X W M hM n₁ X₁ H j₀ j₁ M₂ hH hM₂ e₁ he hB hXW
  obtain ⟨c, hc⟩ := GlobalTheory.T.additive_homogeneous_functional_linear hKP F E σ B n d X W M hB hM hXW
    (fun φ => (∑' w : Fin d → E, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ))))) hl.1 hl.2
    (GlobalTheory.T.adapted_mixed_model_support hKP F E σ B n d X W M hM n₁ X₁ H j₀ j₁ M₂ hH hM₂ e₁ he hB hXW)
    (GlobalTheory.T.adapted_mixed_model_equivariance hKP F E σ B n d X W M hM n₁ X₁ H j₀ j₁ M₂ hH hM₂ e₁ he hB hXW)
  obtain ⟨φ₀, hφ₀, hne⟩ := GlobalTheory.T.adapted_mixed_model_vanishing hKP F E σ B n d X W M hM n₁ X₁ H j₀ j₁ M₂ hH hM₂ e₁ he hB hXW
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hc φ₀ hφ₀)
  refine ⟨c⁻¹, inv_ne_zero hc0, ⟨φ₀, hφ₀, fun h0 => hne ?_⟩, fun φ hφ => ?_⟩
  · have := hc φ₀ hφ₀
    beta_reduce at this
    rw [this, h0, mul_zero]
  · have := hc φ hφ
    beta_reduce at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

private theorem swapX (hKP : KP) (hP : IsPair B M χX χW om r s r' s') (hP₂ : IsPair B M₂ χX χW om₂ r₁ s₁ r' s')
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (he : IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁)
    (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)) (h1 : μ 𝓕 = 1) {Ψ : Fn F n d} (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    Summable (fun w : Fin d → E => ∫ u in 𝓕, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) ∂μ) ∧
      ∫ u in 𝓕, (∑' w : Fin d → E, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ)))) ∂μ =
        ∑' w : Fin d → E, ∫ u in 𝓕, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) ∂μ := by
  haveI := GlobalTheory.ThKSwap.countable_of_numberField E
  have hψ := hP.base.std
  have hS := hP.weil.isUSplitting
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n₁ × Fin d)
  let l : (Fin d → E) → Fn F n d →ₗ[ℂ] ℂ := fun w =>
    (l₀ ∘ₗ e₁) ∘ₗ GlobalTheory.ConeMeasV.schrLin B.ψ (M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w)))
  have hl : ∀ w, l w ∈ (adeleClass F).adm (Fin n × Fin d) := fun w =>
    GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ _ (GlobalTheory.ConeMeasV.comp_ev_mem_adm hP.good hP₂.good he hl₀)
  have hleq : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d),
      l w Φ = thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Φ)) := fun w Φ hΦ =>
    hl₀eq _ (he.maps _ (GlobalTheory.ConeMeasV.schr_mem_schA hψ _ hΦ))
  have hsum : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun w => ‖l w Φ‖ := fun Φ hΦ => by
    simp_rw [fun w => hleq w Φ hΦ]
    exact (summable_norm_iff (E := ℂ)).mpr (GlobalTheory.T.adapted_mixed_model_evaluation hKP F E σ B n d X W M hP.good n₁ X₁ H j₀ j₁ M₂ hH hP₂.good e₁ he hP.base
      ⟨r, s, r', s', hP.herm, hP.skew⟩ Φ hΦ)
  obtain ⟨K, hK, hcov⟩ := UpperTheory.unipotent_compact_fundamental_domain F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hP.base hP.herm hP₂.herm hH
  have hK' : IsCompact ((fun u : unip σ X H => ((u.1, 1) : UA σ X.J × UA σ W.J)) '' K) :=
    hK.image (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, hC⟩ := UpperTheory.theta_countable_functional_bound F E σ B n d X W M χX χW om r s r' s' hP _ l hl hsum Ψ hΨ _ hK'
  refine GlobalTheory.ThKSwap.swap_of_bound μ 𝓕 (by simp [h1]) _ (fun w => ?_) C fun u => ?_
  · have hc := (hS.cont _ (hl w) Ψ hΨ).comp
      (continuous_subtype_val.prodMk continuous_const : Continuous fun u : unip σ X H => ((u.1, 1) : UA σ X.J × UA σ W.J))
    refine (hc.congr fun u => ?_).aestronglyMeasurable
    exact hleq w _ (hS.pres _ _ hΨ)
  · obtain ⟨γ, hγ, hk⟩ := hcov u
    have key : ∀ w : Fin d → E, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) Ψ))) = l w (om ((γ * u).1, 1) Ψ) := fun w => by
      rw [hleq w _ (hS.pres _ _ hΨ)]
      exact (UpperTheory.theta_pair_plane_integral hKP F E σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he w γ.1
        (Subgroup.mem_subgroupOf.1 hγ) γ.2 u.1 Ψ hΨ).symm
    simp_rw [key]
    exact ⟨hsum _ (hS.pres _ _ hΨ), hC _ ⟨_, hk, rfl⟩⟩

private theorem phase_mul (hH : H.IsAdapted σ B X X₁ j₀ j₁) (w : Fin n₁ → E) {u v : UA σ X.J} (hu : u ∈ unip σ X H)
    (hv : v ∈ unip σ X H) :
    GlobalTheory.IsoPhase.phase σ X H w (u * v) = GlobalTheory.IsoPhase.phase σ X H w u + GlobalTheory.IsoPhase.phase σ X H w v := by
  rw [GlobalTheory.UnipCT.unip_eq] at hu hv
  have hui := (GlobalTheory.UnipCT.unipSet σ X H).inv_mem hu
  set a : Fin n → AE F E := incV F (H.ι *ᵥ w) with ha
  set x : Fin n → AE F E := incV F H.x
  set y : Fin n → AE F E := incV F H.y
  have haY : GlobalTheory.UnipMass.hA σ X.J a y = 0 := by
    rw [ha, GlobalTheory.UnipMass.hA_incV, (hH.orth w).2, map_zero]
  set t : Fin n → AE F E := mat u⁻¹ *ᵥ y - y with ht
  have hXt : GlobalTheory.UnipMass.hA σ X.J x t = 0 := by
    have hx : mat u⁻¹ *ᵥ x = x := hui.1
    have h1 := GlobalTheory.IsoPhaseAdd.hA_mat_mulVec σ u⁻¹ x y
    rw [hx] at h1
    have h2 : mat u⁻¹ *ᵥ y = t + y := by rw [ht, sub_add_cancel]
    rw [h2, GlobalTheory.UnipMass.hA_add_right] at h1
    exact add_eq_right.1 h1
  obtain ⟨c, hc⟩ := hv.2 (incV F w)
  rw [GlobalTheory.UnipMass.incM_mulVec_incV] at hc
  have hc' : mat v *ᵥ a = a + c • x := hc
  have hvt : GlobalTheory.UnipMass.hA σ X.J a (mat v⁻¹ *ᵥ t) = GlobalTheory.UnipMass.hA σ X.J a t := by
    have h1 := GlobalTheory.IsoPhaseAdd.hA_mat_mulVec σ v a (mat v⁻¹ *ᵥ t)
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.UnipCT.mat_mul', mul_inv_cancel, hc'] at h1
    have h3 : mat (1 : UA σ X.J) = 1 := rfl
    rw [h3, Matrix.one_mulVec, add_comm, GlobalTheory.IsoPhaseAdd.hA_smul_add_left, hXt, mul_zero, zero_add] at h1
    exact h1.symm
  have key : GlobalTheory.UnipMass.hA σ X.J a (mat (u * v)⁻¹ *ᵥ y) =
      GlobalTheory.UnipMass.hA σ X.J a (mat u⁻¹ *ᵥ y) + GlobalTheory.UnipMass.hA σ X.J a (mat v⁻¹ *ᵥ y) := by
    have e1 : mat u⁻¹ *ᵥ y = y + t := by rw [ht, add_sub_cancel]
    rw [mul_inv_rev, GlobalTheory.UnipCT.mat_mul', ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_add, GlobalTheory.UnipMass.hA_add_right,
      hvt, GlobalTheory.UnipMass.hA_add_right, haY, zero_add, add_comm]
  unfold GlobalTheory.IsoPhase.phase
  rw [← ha, key, map_add, neg_add]

private theorem phase_cont (X : Spc F E n) (H : Plane E n n₁) (w : Fin n₁ → E) :
    Continuous fun u : UA σ X.J => GlobalTheory.IsoPhase.phase σ X H w u := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hm : Continuous fun u : UA σ X.J => mat u⁻¹ := Units.continuous_coe_inv.comp continuous_subtype_val
  have hv : Continuous fun u : UA σ X.J => mat u⁻¹ *ᵥ incV F H.y := hm.matrix_mulVec continuous_const
  unfold GlobalTheory.IsoPhase.phase GlobalTheory.UnipMass.hA
  refine (htr.comp ?_).neg
  refine continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_pi fun i => hc.comp ?_))
  exact (continuous_apply i).comp hv

private theorem isoInner (hKP : KP) (hP : IsPair B M χX χW om r s r' s') (hP₂ : IsPair B M₂ χX χW om₂ r₁ s₁ r' s')
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (he : IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁)
    (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (he₀ : IsEv B M₂ M₃ 1 H'.ι (iso0 n₁ H') e₀) (C : ℂ)
    (hexp : ∀ φ ∈ schA F (Fin n₁ × Fin d),
      Summable (fun ξ : Fin n₁ → E => thetaSum F (e₀ (M₂.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) φ))) ∧
      thetaSum F φ = C * ∑' ξ : Fin n₁ → E, thetaSum F (e₀ (M₂.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) φ)))
    (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ) (h1 : μ 𝓕 = 1)
    {Ψ : Fn F n d} (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    ∫ u in 𝓕, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u.1, 1) Ψ))) ∂μ =
      C * thetaSum F (e₀ (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ))) := by
  haveI := GlobalTheory.ThKSwap.countable_of_numberField E
  have hψ := hP.base.std
  have hS := hP.weil.isUSplitting
  have hφ : ∀ Φ ∈ schA F (Fin n × Fin d), e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Φ) ∈
      schA F (Fin n₁ × Fin d) := fun Φ hΦ => he.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ)
  set a : (Fin n₁ → E) → ℂ := fun ξ => thetaSum F (e₀ (M₂.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y))
          (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ)))) with ha
  have hlaw : ∀ (ξ : Fin n₁ → E) (u : unip σ X H), thetaSum F (e₀ (M₂.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y))
          (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u.1, 1) Ψ))))) =
      B.ψ (-GlobalTheory.IsoPhase.phase σ X H ξ u.1) * a ξ := fun ξ u =>
    UpperTheory.pair_restricts_along_adapted_plane hKP F E σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he d₁ W₁ H' i₀ i₁ M₃ hH'
      e₀ he₀ ξ u.1 u.2 Ψ hΨ
  have hpt : ∀ u : unip σ X H, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u.1, 1) Ψ))) =
      C * ∑' ξ : Fin n₁ → E, B.ψ (-GlobalTheory.IsoPhase.phase σ X H ξ u.1) * a ξ := fun u => by
    rw [(hexp _ (hφ _ (hS.pres _ _ hΨ))).2]
    simp_rw [hlaw]
  have hsa : Summable fun ξ => ‖a ξ‖ := (summable_norm_iff (E := ℂ)).mpr (hexp _ (hφ _ hΨ)).1
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    GlobalTheory.ThKIsoSwap.integral_tsum_of_bound μ 𝓕 (by simp [h1])
      (fun (ξ : Fin n₁ → E) (u : unip σ X H) => B.ψ (-GlobalTheory.IsoPhase.phase σ X H ξ u.1) * a ξ)
      (fun ξ => ((hψ.1.comp ((phase_cont X H ξ).comp continuous_subtype_val).neg).mul continuous_const).aestronglyMeasurable)
      (∑' ξ, ‖a ξ‖) (fun u => by
        simp_rw [norm_mul, GlobalTheory.StdCharFromIsStd.norm_psi hψ, one_mul]
        exact ⟨hsa, le_rfl⟩), tsum_eq_single 0]
  · have h0 : ∀ u : unip σ X H, GlobalTheory.IsoPhase.phase σ X H 0 u.1 = 0 := fun u => by
      have : incV F (H.ι *ᵥ (0 : Fin n₁ → E)) = 0 := by
        funext i; simp [incV]
      rw [GlobalTheory.IsoPhase.phase, GlobalTheory.UnipMass.hA, this, zero_dotProduct, map_zero, neg_zero]
    have hz : Matrix.vecMulVec (incV F (0 : Fin n₁ → E)) (incV F H'.y) = 0 := by
      ext i j; simp [incV, Matrix.vecMulVec_apply]
    have hrho0 : ∀ φ : Fn F n₁ d, M₂.co.rho B.ψ (Matrix.vecMulVec (incV F (0 : Fin n₁ → E)) (incV F H'.y)) φ = φ := by
      intro φ; funext x; simp [hz, Darboux.rho, schr]
    simp only [h0, neg_zero, AddChar.map_zero_eq_one, one_mul, setIntegral_const, measureReal_def, h1, ENNReal.toReal_one,
      one_smul, ha, hrho0]
  · intro ξ hξ
    obtain ⟨g, hg, hψg⟩ := UpperTheory.unipotent_phase_nontrivial F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hP.base hP.herm hP₂.herm hH ξ hξ
    haveI := hμ
    refine GlobalTheory.IsoPhase.setIntegral_eq_zero_of_mul_right σ X H μ 𝓕 h𝓕 h1
      (fun u : unip σ X H => B.ψ (-GlobalTheory.IsoPhase.phase σ X H ξ u.1) * a ξ) ?_ ⟨g, hg⟩ _ hψg ?_
    · intro γ hγ x
      obtain ⟨c, hc⟩ := GlobalTheory.T.isotropic_phase_rational_value F E σ n n₁ X H ξ γ.1 (Subgroup.mem_subgroupOf.1 hγ)
      simp only [Subgroup.coe_mul]
      rw [phase_mul hH ξ γ.2 x.2, neg_add, AddChar.map_add_eq_mul, hc, ← map_neg, hψ.2.1, one_mul]
    · intro x
      simp only [Subgroup.coe_mul]
      rw [phase_mul hH ξ x.2 hg, neg_add, AddChar.map_add_eq_mul]
      ring

private theorem move (hKP : KP) (hP : IsPair B M χX χW om r s r' s') (hP₂ : IsPair B M₂ χX χW om₂ r₁ s₁ r' s')
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (he : IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁)
    {w w' : Fin d → E} {γ : UA σ W.J} (hγ : γ ∈ ratU σ W.J) (hw : mat γ *ᵥ incV F w = incV F w') (u : UA σ X.J)
    {Ψ : Fn F n d} (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) Ψ))) =
      thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w')) (om (u, 1) (om (1, γ) Ψ)))) := by
  have hS := hP.weil.isUSplitting
  have hu : om (u, 1) Ψ ∈ schA F (Fin n × Fin d) := hS.pres _ _ hΨ
  have hr := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std (Matrix.vecMulVec (incV F H.y) (incV F w)) _ hu
  rw [← GlobalTheory.T.thetaSum_invariant_rational_unitary hKP.base F E σ B n₁ d X₁ W M₂ χX χW om₂ r₁ s₁ r' s' hP₂ 1 (one_mem _) γ hγ _ (he.maps _ hr),
    ← GlobalTheory.T.adapted_plane_pair_local_factor hKP.base F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₂ om₂ r₁ s₁ hH hP₂ e₁ he γ _ hr,
    hS.impl (1, γ) _ _ hu]
  have hact : actAB (cA σ) ((1, γ) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec (incV F H.y) (incV F w)) =
      Matrix.vecMulVec (incV F H.y) (incV F w') := by
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * Matrix.vecMulVec (incV F H.y) (incV F w) * (mat γ)ᵀ = _
    rw [Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hw]
  rw [hact, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

private theorem comp_laws (he : IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁) (he₀ : IsEv B M₂ M₃ 1 H'.ι (iso0 n₁ H') e₀) :
    (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d),
      (e₀ ∘ₗ e₁) (M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = M₃.co.rho B.ψ z ((e₀ ∘ₗ e₁) Φ)) ∧
    (∀ u ∈ isoB H H', ∀ Φ ∈ schA F (Fin n × Fin d), (e₀ ∘ₗ e₁) (M.co.rho B.ψ u Φ) = (e₀ ∘ₗ e₁) Φ) ∧
    ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
      (∀ v, ev v (M.vac v) = M₃.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
        (e₀ ∘ₗ e₁) (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
  have hh : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e₁ (M.co.rho B.ψ (incM F H.ι * z) Φ) = M₂.co.rho B.ψ z (e₁ Φ) := fun z Φ hΦ => by
    have h1 := he.Heisenberg₂ z Φ hΦ
    rwa [GlobalTheory.ThK.IsoComp.incM_one, Matrix.transpose_one, Matrix.mul_one] at h1
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_, ?_⟩
  · have h2 := he₀.Heisenberg₂ z (e₁ Φ) (he.maps Φ hΦ)
    rw [GlobalTheory.ThK.IsoComp.incM_one, Matrix.one_mul] at h2
    simp only [LinearMap.comp_apply]
    rw [Matrix.mul_assoc, hh _ Φ hΦ, h2]
  · simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨y, rfl⟩
    · rw [he.inv u hu Φ hΦ]
    · rw [← Matrix.mul_vecMulVec, hh _ Φ hΦ, he₀.inv _ ⟨y, rfl⟩ _ (he.maps Φ hΦ)]
  · obtain ⟨ei₀, ev₀, -, h0v, h0loc⟩ := he.loc
    obtain ⟨ei', ev', -, h1v, h1loc⟩ := he₀.loc
    have hSB : ∀ v, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev₀ v φ ∈ SB (Fin n₁ × Fin d → Fv F v) := fun v φ hφ => by
      rw [← (h0v v).2]
      exact Submodule.mem_map_of_mem hφ
    refine ⟨ei'.comp ei₀, fun v => ev' v ∘ₗ ev₀ v, fun v => ⟨?_, ?_⟩, fun f φ hφ hφv => ?_⟩
    · simp only [LinearMap.comp_apply]
      rw [(h0v v).1, (h1v v).1]
    · rw [Submodule.map_comp, (h0v v).2, (h1v v).2]
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [h0loc f φ hφ hφv, h1loc (ei₀ f) (fun v => ev₀ v (φ v)) (fun v => hSB v _ (hφ v))]
      filter_upwards [hφv] with v hv
      rw [hv, (h0v v).1]

private theorem comp_ne (hψ : IsStd B.ψ) (he : IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁) {C C' : ℂ}
    (hne : ∃ Ψ ∈ schA F (Fin n × Fin d), thetaSum F Ψ ≠ 0)
    (h₁ : ∀ Ψ ∈ schA F (Fin n × Fin d),
      thetaSum F Ψ = C * ∑' w : Fin d → E, thetaSum F (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ)))
    (h₂ : ∀ φ ∈ schA F (Fin n₁ × Fin d),
      thetaSum F φ = C' * ∑' ξ : Fin n₁ → E, thetaSum F (e₀ (M₂.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) φ))) :
    ∃ Ψ ∈ schA F (Fin n × Fin d), e₀ (e₁ Ψ) ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨Ψ, hΨ, hne⟩ := hne
  have h0 : ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e₁ Φ) = 0 := fun Φ hΦ => by
    have hz : ∀ ξ : Fin n₁ → E, thetaSum F (e₀ (M₂.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (e₁ Φ))) = 0 := fun ξ => by
      rw [← he.Heisenberg₂ _ Φ hΦ, h _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ)]
      simp [thetaSum]
    rw [h₂ _ (he.maps Φ hΦ)]
    simp [hz]
  apply hne
  rw [h₁ Ψ hΨ]
  simp [fun w : Fin d → E => h0 _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ (Matrix.vecMulVec (incV F H.y) (incV F w)) _ hΨ)]

private theorem pair_mid (hKP : KP) {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} (hG₁ : G₁.IsGood B) {Y : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G Y om om') {M₂ : Model σ G₁.V' G.W} (hM₂ : M₂.IsGood B.ψ) :
    ∃ om₂, IsPair B M₂ Y.α (Y.α / Y.β) om₂ G₁.q (b - G₁.q) (a + (b + 2) - (G.p + G.q)) (G.p + G.q) := by
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range Y.α b := by
    intro x
    rw [hP.resX x, pow_add, neg_one_sq, mul_one]
  obtain ⟨om₂, h⟩ := GlobalTheory.T.hecke_characters_restriction_eta hKP.base F E σ B hT.base b _ G₁.V' G.W _ _ _ _ hG₁.hV' hP.skew M₂ hM₂ _ _ hP.hX hP.hW hres hP.resW
  exact ⟨om₂, hT.base, hG₁.hV', hP.skew, hM₂, hP.hX, hP.hW, hres, hP.resW, h⟩

end GlobalTheory.ConeSmallUnf.CTerm

end

open GlobalTheory.ConeSmallUnf.CTerm in
theorem _root_.GlobalTheory.T.config_b_witt_constant_nonzero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∃ C₀ : ℂ, C₀ ≠ 0 ∧ (∃ γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ) ∧
      ∀ γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, (∀ g, Summable fun w => termW B G.M' H H' e' om' Φ' γ w g h) ∧
        IsCT H (fun g => theta om' Φ' g h) fun g => C₀ * ∑' w, termW B G.M' H H' e' om' Φ' γ w g h := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he'
  have hH := hC.hH
  have hH' := hC.hH'
  have hWitt : ∃ γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ := by
    obtain ⟨h1, h2, l, h3, h4⟩ := UpperTheory.skew_form_hermitian_twist F E σ _ _ G.V' G.W G.M' H.x H.y H'.x H'.y hH.xy hH'.xy
    refine UpperTheory.exists_witt_partner F E σ _ G.W.J l h1 h2 h3 h4 H'.x (fun h0 => ?_) hH'.xx
    have := hH'.xy
    simp [form, h0] at this
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, hWitt, fun γ _ X om om' om₁ om₁' hT hT₁ => absurd ⟨X, om, om', om₁, om₁', hT, hT₁⟩ hex⟩
  obtain ⟨X₀, o, o', o₁, o₁', hT₀, hT₀'⟩ := hex
  have hB := hT₀.base
  have hG := hT₀.geo
  have hG₁ := hT₀'.geo
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B hB _ _ G₁.V' G.W _ _ _ _ hG₁.hV' hG.hW
  obtain ⟨o₂, hQ₂⟩ := pair_mid hKP hG₁ hT₀ hM₂
  have hQ := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₀).2
  obtain ⟨e₁, he⟩ := GlobalTheory.T.adapted_plane_pair_restriction hKP.base F E σ B _ _ G.V' G.W G.M' _ _ o' _ _ _ _ hQ b G₁.V' H _ _ M₂ o₂ _ _ hH hQ₂
  obtain ⟨e₀, he₀⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B _ _ G₁.V' G.W M₂ _ _ o₂ _ _ _ _ hQ₂ _ G₁.V' G₁.W H' _ _ G₁.M' rfl hH'
    hG₁.hM').1
  obtain ⟨C₁, hC₁, hne, hexp₁⟩ := expandX hKP hB hG.hV' hG.hW hG.hM' hM₂ hH he
  obtain ⟨C₂, hC₂, hexp₂⟩ := GlobalTheory.T.eigen_intertwiner_restriction_rank hKP F E σ B _ _ _ G₁.V' G.W G₁.W M₂ G₁.M' H' _ _ hH' hG₁.hM' e₀ he₀ hB hM₂
    ⟨_, _, _, _, hG₁.hV', hG.hW⟩
  obtain ⟨c1, c2, c3⟩ := comp_laws he he₀
  obtain ⟨c, hc⟩ := GlobalTheory.T.config_b_triple_evaluation_compatible hKP.base F E σ B a b G G₁ H H' hC X₀ o o' o₁ o₁' hT₀ hT₀' e' he' (e₀ ∘ₗ e₁)
    (fun Φ hΦ => he₀.maps _ (he.maps Φ hΦ)) c1 c2 c3
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨Ψ, hΨ, h⟩ := comp_ne hB.std he hne hexp₁ (fun φ hφ => (hexp₂ φ hφ).2)
    exact h (by simpa using hc Ψ hΨ)
  refine ⟨C₁ * (C₂ * c), mul_ne_zero hC₁ (mul_ne_zero hC₂ hc0), hWitt, ?_⟩
  intro γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  obtain ⟨om₂, hP₂⟩ := pair_mid hKP hG₁ hT hM₂
  have hS := hP.weil.isUSplitting
  have hΦs : Φ' ∈ schA F _ := GlobalTheory.ConeMeasV.polData_le_schA hG.hM' hΦ'.1
  have hsh : shiftB σ H H' 1 = Matrix.vecMulVec (incV F H.y) (incV F H'.x) := by simp [shiftB]

  have hiso : ∀ (μ : Measure (unip σ G.V' H)) (𝓕 : Set (unip σ G.V' H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ G.V'.J).subgroupOf (unip σ G.V' H)) 𝓕 μ → μ 𝓕 = 1 → ∀ g (w : IsoV σ G.W.J),
      ∫ u in 𝓕, thetaSum F (e₁ (G.M'.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w.1)) (om' (u.1, 1) (om' (g, h) Φ')))) ∂μ =
        C₂ * c * termW B G.M' H H' e' om' Φ' γ w g h := by
    intro μ 𝓕 hμ h𝓕 h1 g w
    have hΨ := hS.pres (g, h) _ hΦs
    have hΨ' := hS.pres (1, γ w) _ hΨ
    simp_rw [fun u => move hKP hP hP₂ hH he (hγ w).1 (hγ w).2 u hΨ]
    rw [isoInner hKP hP hP₂ hH he hH' he₀ C₂ hexp₂ μ 𝓕 hμ h𝓕 h1 hΨ']
    have e1 : ((g, γ w * h) : UA σ G.V'.J × UA σ G.W.J) = (1, γ w) * (g, h) := by simp
    have e2 := hc _ (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hB.std (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) _ hΨ')
    rw [LinearMap.comp_apply] at e2
    rw [e2, GlobalTheory.ThKIsoSwap.thetaSum_smul, termW, hsh, e1, map_mul, Module.End.mul_apply, mul_assoc]
  refine ⟨fun g => ?_, ?_⟩
  · obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.unipotent_haar_fundamental_domain_unit F E σ G.V' H
      (UpperTheory.unipotent_compact_fundamental_domain F E σ B _ _ G.V' G₁.V' H _ _ _ _ _ _ hB hG.hV' hG₁.hV' hH)
    have hs := (swapX hKP hP hP₂ hH he μ 𝓕 h1 (hS.pres (g, h) _ hΦs)).1
    have hs' := (hs.comp_injective (i := fun w : IsoV σ G.W.J => w.1) Subtype.val_injective).mul_left (C₂ * c)⁻¹
    refine hs'.congr fun w => ?_
    simp only [Function.comp_apply]
    rw [hiso μ 𝓕 hμ h𝓕 h1 g w, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hC₂ hc0), one_mul]
  · intro μ 𝓕 hμ h𝓕 h1 g
    have hΨ := hS.pres (g, h) _ hΦs
    obtain ⟨-, hsw⟩ := swapX hKP hP hP₂ hH he μ 𝓕 h1 hΨ
    have hpt : ∀ u : unip σ G.V' H, theta om' Φ' (u.1 * g) h =
        C₁ * ∑' w, thetaSum F (e₁ (G.M'.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om' (u.1, 1) (om' (g, h) Φ')))) := fun u => by
      have e1 : ((u.1 * g, h) : UA σ G.V'.J × UA σ G.W.J) = (u.1, 1) * (g, h) := by simp
      rw [theta, e1, map_mul, Module.End.mul_apply]
      exact hexp₁ _ (hS.pres _ _ hΨ)
    beta_reduce
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hsw, mul_assoc]
    congr 1
    have hsupp : Function.support (fun w => ∫ u in 𝓕, thetaSum F (e₁ (G.M'.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om' (u.1, 1) (om' (g, h) Φ')))) ∂μ) ⊆
        {w | w ≠ 0 ∧ form σ G.W.J w w = 0} := by
      intro w hw
      refine ⟨?_, ?_⟩
      · rintro rfl
        apply hw
        have hz : Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin (a + (b + 2)) → E)) = 0 := by
          ext i j; simp [incV, Matrix.vecMulVec_apply]
        have hrho0 : ∀ φ : Fn F (b + 2) (a + (b + 2)),
            G.M'.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin (a + (b + 2)) → E))) φ = φ := by
          intro φ; funext x; simp [hz, Darboux.rho, schr]
        have hst := GlobalTheory.T.weil_representation_preserves_space hKP.base F E σ B _ _ G X om om' hT
        have h0 : ∀ u : unip σ G.V' H, e₁ (om' (u.1, 1) (om' (g, h) Φ')) = 0 := fun u =>
          UpperTheory.theta_pair_plane_unipotent hKP F E σ B _ _ _ G.V' G.W G₁.V' G.M' M₂ H _ _ _ _ om' om₂ _ _ _ _ _ _ hP hP₂ hH e₁ he _ B.τ₁ _
            (hst _ _ (hst _ _ hΦ'.2))
        simp [hrho0, h0, thetaSum]
      · by_contra hf
        exact hw (UpperTheory.pair_restriction_compatible_with_models hKP F E σ B _ _ _ G.V' G.W G₁.V' G.M' M₂ H _ _ _ _ om' om₂ _ _ _ _ _ _ hP hP₂ hH e₁ he μ 𝓕 hμ h𝓕 h1
          _ hΨ w hf)
    rw [← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]
    exact tsum_congr fun w => (hiso μ 𝓕 hμ h𝓕 h1 g w).symm
