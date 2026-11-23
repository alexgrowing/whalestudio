import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralUnipotentTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapPairCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapPairCompatAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.AnisConstTerm

set_option synthInstance.maxHeartbeats 400000 in

theorem integral_anisotropic_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ ξ : Fin n → E, form σ X.J ξ ξ ≠ 0 →
      ∫ u in 𝓕, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ))) ∂μ = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he₀ χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 Ψ hΨ ξ hξ
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ W.J) := inferInstance
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  obtain ⟨κ, hκ, hph⟩ := GlobalTheory.T.eval_map_pair_compat hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he₀ χX χW om r s r' s' hP ξ hξ
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.T.standard_adelic_char_exists_ne_one F B.ψ hP.base.std
  let k : (AF F)ˣ := Units.map (algebraMap F (AF F) : F →* AF F) (Units.mk0 κ hκ)
  have ht : (s₀ * ((k⁻¹ : (AF F)ˣ) : AF F)) * algebraMap F (AF F) κ = s₀ := by
    rw [mul_assoc, show algebraMap F (AF F) κ = (k : AF F) from rfl, Units.inv_mul, mul_one]
  obtain ⟨z, hzU, hzc, hzy⟩ := GlobalTheory.T.exists_central_unipotent_translate F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hP.base.cm hP.skew hH (s₀ * ((k⁻¹ : (AF F)ˣ) : AF F))
  set T : UA σ W.J → ℂ := fun u => thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u) Ψ))) with hTdef
  have hT : ∀ u, T (z * u) = B.ψ s₀ * T u := fun u => by
    have := hph _ z hzU hzy u Ψ hΨ
    rw [ht] at this
    exact this
  have hR : ∀ γ ∈ ratU σ W.J, γ ∈ unip σ W H' → ∀ u, T (γ * u) = T u := fun γ hγ hγU u =>
    GlobalTheory.T.eval_map_pair_compat_alt hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he₀ χX χW om r s r' s' hP ξ γ hγ hγU u Ψ hΨ

  set z' : unip σ W H' := ⟨z, hzU⟩
  haveI : Countable ((ratU σ W.J).subgroupOf (unip σ W H')) := GlobalTheory.UnipMass.countable_ratU' σ W.J (unip σ W H')
  letI : MeasurableSpace ((ratU σ W.J).subgroupOf (unip σ W H')) := ⊤
  haveI : MeasurableSMul ((ratU σ W.J).subgroupOf (unip σ W H')) (unip σ W H') :=
    { measurable_const_smul := fun c => measurable_const_mul (c : unip σ W H')
      measurable_smul_const := fun _ => measurable_from_top }
  haveI : SMulInvariantMeasure ((ratU σ W.J).subgroupOf (unip σ W H')) (unip σ W H') μ :=
    ⟨fun c _ _ => measure_preimage_mul μ (c : unip σ W H') _⟩
  let f : unip σ W H' ≃ᵐ unip σ W H' := MeasurableEquiv.mulLeft z'
  have hpres : MeasurePreserving f μ μ := measurePreserving_mul_left μ z'
  have h𝓕' : IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) (f ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro g x
    apply Subtype.ext
    show z * ((g : unip σ W H') * x : unip σ W H').1 = ((g : unip σ W H') : UA σ W.J) * (z * x.1)
    rw [Subgroup.coe_mul, ← mul_assoc, hzc _ (g : unip σ W H').2, mul_assoc]
  have hinvz : ∀ (g : (ratU σ W.J).subgroupOf (unip σ W H')) (x : unip σ W H'), T (z * (g • x).1) = T (z * x.1) := by
    intro g x
    show T (z * ((g : unip σ W H') * x : unip σ W H').1) = _
    rw [Subgroup.coe_mul, ← mul_assoc, hzc _ (g : unip σ W H').2, mul_assoc]
    exact hR _ (Subgroup.mem_subgroupOf.1 g.2) (g : unip σ W H').2 _
  have A : ∫ u in 𝓕, T (z * u.1) ∂μ = ∫ u in f ⁻¹' 𝓕, T (z * u.1) ∂μ := h𝓕.setIntegral_eq h𝓕' hinvz
  have B' : ∫ u in f ⁻¹' 𝓕, T (z * u.1) ∂μ = ∫ u in 𝓕, T u.1 ∂μ :=
    hpres.setIntegral_preimage_emb f.measurableEmbedding (fun u : unip σ W H' => T u.1) 𝓕
  have C : ∫ u in 𝓕, T (z * u.1) ∂μ = B.ψ s₀ * ∫ u in 𝓕, T u.1 ∂μ := by
    simp_rw [hT]; exact integral_const_mul _ _
  have D : (B.ψ s₀ - 1) * ∫ u in 𝓕, T u.1 ∂μ = 0 := by
    rw [sub_mul, ← C, A, B', one_mul, sub_self]
  exact (mul_eq_zero.1 D).resolve_left (sub_ne_zero.2 hs₀)

end GlobalTheory.AnisConstTerm
