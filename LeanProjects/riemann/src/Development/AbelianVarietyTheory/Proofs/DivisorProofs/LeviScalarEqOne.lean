import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairTransferStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixedPlane

open scoped Classical in

theorem eval_mem_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F), (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro F _ _ κ _ x g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem levi_scalar_eq_one : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      (∀ h₁ m, IsLevi H' 1 h₁ m → ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = c • om₁ (1, h₁) (e Φ)) →
      ∀ h₁ m, IsLevi H' 1 h₁ m → ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = om₁ (1, h₁) (e Φ) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he hc
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hσσ : ∀ z : E, σ (σ z) = z := by
    intro z
    obtain ⟨-, -, -, hτ⟩ := hP.base.cm
    let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    apply τ.injective
    rw [hτ, hτ, star_star]
  choose mf hmf hmu using GlobalTheory.T.exists_unique_levi_element F E σ B d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hσσ hP.skew hP₁.skew hH
  choose c₀ hc₀ using fun h₁ => hc h₁ (mf h₁) (hmf h₁)
  obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := GlobalTheory.T.eigen_intertwiner_restriction F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  have inv1 : ∀ (m : UA σ W.J) (Φ : Fn F n d), om (1, m) (om (1, m⁻¹) Φ) = Φ := by
    intro m Φ
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have inj1 : ∀ (h : UA σ W₁.J) (v : Fn F n d₁), om₁ (1, h) v = 0 → v = 0 := by
    intro h v hv
    have := congrArg (om₁ (1, h⁻¹)) hv
    rwa [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply, map_zero] at this
  have hv : ∀ h, om₁ (1, h) (e Φ₀) ≠ 0 := fun h h0 => hΦ₀ne (inj1 h _ h0)
  have uniq : ∀ h a, (∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, mf h) Φ) = a • om₁ (1, h) (e Φ)) → a = c₀ h := by
    intro h a ha
    exact smul_left_injective ℂ (hv h) ((ha Φ₀ hΦ₀).symm.trans (hc₀ h Φ₀ hΦ₀))
  have hne : ∀ h, c₀ h ≠ 0 := by
    intro h h0
    apply hΦ₀ne
    have := hc₀ h (om (1, (mf h)⁻¹) Φ₀) (hs.pres _ _ hΦ₀)
    rwa [inv1, h0, zero_smul] at this
  have hm : ∀ h h', IsLevi H' 1 (h * h') (mf h * mf h') := by
    intro h h'
    obtain ⟨a1, a2, a3⟩ := hmf h
    obtain ⟨b1, b2, b3⟩ := hmf h'
    simp only [Units.val_one, one_smul, inv_one, map_one] at a1 a2 b1 b2
    refine ⟨?_, ?_, ?_⟩
    · change (mat (mf h) * mat (mf h')) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b1, a1, Units.val_one, one_smul]
    · change (mat (mf h) * mat (mf h')) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, b2, a2, inv_one, Units.val_one, map_one, one_smul]
    · change (mat (mf h) * mat (mf h')) * _ = _ * (mat h * mat h')
      rw [Matrix.mul_assoc, b3, ← Matrix.mul_assoc, a3, Matrix.mul_assoc]
  have hmul : ∀ h h', c₀ (h * h') = c₀ h * c₀ h' := by
    intro h h'
    refine (uniq (h * h') _ fun Φ hΦ => ?_).symm
    rw [← hmu (h * h') _ (hm h h')]
    have e1 : ((1 : UA σ X.J), mf h * mf h') = (1, mf h) * (1, mf h') := by
      rw [Prod.mk_mul_mk, mul_one]
    have e2 : ((1 : UA σ X.J), h * h') = (1, h) * (1, h') := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [e1, map_mul, Module.End.mul_apply, hc₀ h _ (hs.pres _ _ hΦ), hc₀ h' _ hΦ, map_smul, smul_smul, e2, map_mul,
      Module.End.mul_apply]
  have hcont : Continuous c₀ := by
    rw [continuous_iff_continuousAt]
    intro h₀
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hΦ₀ne
    have hΦ : om (1, (mf h₀)⁻¹) Φ₀ ∈ schA F (Fin n × Fin d) := hs.pres _ _ hΦ₀
    have hmc : Continuous mf := GlobalTheory.T.continuous_of_forall_isLevi F E σ B d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hP.skew hP₁.skew hH mf hmf
    have hN : Continuous fun h => e (om (1, mf h) (om (1, (mf h₀)⁻¹) Φ₀)) x := by
      have hl := GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
        (LinearMap.proj x) (eval_mem_adm F (Fin n × Fin d₁) x)
      exact (hP.weil.2.2 _ hl _ hΦ).comp (continuous_const.prodMk hmc)
    have hG : Continuous fun h => om₁ (1, h) (e (om (1, (mf h₀)⁻¹) Φ₀)) x :=
      (hP₁.weil.2.2 _ (eval_mem_adm F (Fin n × Fin d₁) x) _ (he.maps _ hΦ)).comp (continuous_const.prodMk continuous_id)
    have hEq : ∀ h, e (om (1, mf h) (om (1, (mf h₀)⁻¹) Φ₀)) x =
        c₀ h * om₁ (1, h) (e (om (1, (mf h₀)⁻¹) Φ₀)) x := fun h => by
      rw [hc₀ h _ hΦ, Pi.smul_apply, smul_eq_mul]
    have hG0 : om₁ (1, h₀) (e (om (1, (mf h₀)⁻¹) Φ₀)) x ≠ 0 := by
      intro h0
      apply hx
      have := hEq h₀
      rwa [inv1, h0, mul_zero] at this
    have hev : (fun h => e (om (1, mf h) (om (1, (mf h₀)⁻¹) Φ₀)) x / om₁ (1, h) (e (om (1, (mf h₀)⁻¹) Φ₀)) x) =ᶠ[𝓝 h₀] c₀ := by
      filter_upwards [hG.continuousAt.eventually_ne hG0] with h hh
      rw [hEq h, mul_div_assoc, div_self hh, mul_one]
    exact (hN.continuousAt.div hG.continuousAt hG0).congr hev
  have h1 : c₀ 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact mul_left_cancel₀ (hne 1) (this.symm.trans (mul_one _).symm)
  let cu : UA σ W₁.J →* ℂˣ :=
    { toFun := fun h => Units.mk0 (c₀ h) (hne h)
      map_one' := Units.ext (by simp [h1])
      map_mul' := fun h h' => Units.ext (by simp [hmul]) }
  have hcu : Continuous cu := by
    rw [Units.continuous_iff]
    refine ⟨hcont, ?_⟩
    convert hcont.inv₀ hne using 1
    funext x
    simp [cu]
  have htriv := GlobalTheory.T.skew_adapted_pair_transfer hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he cu hcu
    (fun h₁ m hl Φ hΦ => by rw [hmu h₁ m hl]; exact hc₀ h₁ Φ hΦ)
  intro h₁ m hl Φ hΦ
  have hc1 : c₀ h₁ = 1 := by
    have := congrArg (fun f : UA σ W₁.J →* ℂˣ => ((f h₁ : ℂˣ) : ℂ)) htriv
    simpa [cu] using this
  rw [hmu h₁ m hl, hc₀ h₁ Φ hΦ, hc1, one_smul]

end GlobalTheory.MixedPlane
