import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKRightInv

open MeasureTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ ξ : E, ξ ≠ 0 ∧ σ ξ = -ξ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  by_contra hne
  push_neg at hne
  have hid : ∀ x, σ x = x := by
    intro x
    by_contra hx
    refine hne (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) ?_
    rw [map_sub, hσ]; ring
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hr : ComplexEmbedding.IsReal w.embedding := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    simpa [hid x, Complex.star_def] using (h.2.2.2 w.embedding x).symm
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hr)

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in

theorem map_mul_right_eq (hS : GlobalTheory.Published.SiegelSetUnitary) {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (B : Base F E) {d r s : ℕ}
    {W : Spc F E d} (hW : W.IsSkew σ B r s) (μ : Measure (UA σ W.J)) [hμ : μ.IsHaarMeasure] (𝓕 : Set (UA σ W.J))
    (h𝓕 : IsFundamentalDomain (ratU σ W.J) 𝓕 μ) (h : UA σ W.J) : μ.map (· * h) = μ := by
  obtain ⟨ξ, hξ0, hξ⟩ := exists_anti hcm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hJ := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B d W r s hW ξ hξ0 hξ
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.ThKContSmall.measure_fundamental_domain_lt_top hS hcm hJ _ (GlobalTheory.SiegelSet.ug_eq_hr hσ hξ0) μ hμ 𝓕 h𝓕
  obtain ⟨htg, hlc, hsc, ht2⟩ := GlobalTheory.UnipCT.topFacts σ W.J
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ W.J
  haveI : MeasurableMul (UA σ W.J) := inferInstance
  haveI : SigmaCompactSpace (UA σ W.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : SFinite μ := inferInstance
  haveI : MeasurableConstSMul (ratU σ W.J) (UA σ W.J) :=
    ⟨fun γ => (measurable_const_mul (γ.1 : UA σ W.J))⟩
  haveI : SMulInvariantMeasure (ratU σ W.J) (UA σ W.J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  haveI : (μ.map (· * h)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ h
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map (· * h)) μ
  set c := Measure.haarScalarFactor (μ.map (· * h)) μ
  have h𝓕' : IsFundamentalDomain (ratU σ W.J) ((· * h) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ h) (e := id) Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : μ ((· * h) ⁻¹' 𝓕) = μ 𝓕 := h𝓕'.measure_eq h𝓕
  have h0 : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hmap : (μ.map (· * h)) 𝓕 = μ ((· * h) ⁻¹' 𝓕) := MeasurableEquiv.map_apply (MeasurableEquiv.mulRight h) 𝓕
  have h1 : (c : ENNReal) * μ 𝓕 = 1 * μ 𝓕 := by
    calc (c : ENNReal) * μ 𝓕 = (c • μ) 𝓕 := by simp [Measure.smul_apply]
      _ = (μ.map (· * h)) 𝓕 := by rw [← hc]
      _ = 1 * μ 𝓕 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin.ne).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end GlobalTheory.ThKRightInv

namespace GlobalTheory.ThKRightInv

open MeasureTheory

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in

theorem setIntegral_mul_right : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, ∫ x in 𝓕, G.M'.I om' Φ (x * h) * starRingEnd ℂ (G.M'.I om' Ψ (x * h)) ∂μ = ∫ x in 𝓕, G.M'.I om' Φ x * starRingEnd ℂ (G.M'.I om' Ψ x) ∂μ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ hΦ Ψ hΨ h
  have hT := hM.triple
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hKP.base
  have hP := GlobalTheory.ThKContSmall.isPair_small hT
  have inv : ∀ Θ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ γ ∈ ratU σ G.W.J, ∀ x,
      G.M'.I om' Θ (γ * x) = G.M'.I om' Θ x :=
    fun Θ hΘ γ hγ x => GlobalTheory.ThKRatInv.I_rat_inv hTB B G.M' hP Θ (Submodule.mem_inf.1 hΘ).1 γ hγ x
  haveI := hμ
  have hR : μ.map (· * h) = μ := map_mul_right_eq hKP.siegelSetUnitary hT.base.cm B hT.geo.hW μ 𝓕 h𝓕 h
  obtain ⟨htg, hlc, hsc, ht2⟩ := GlobalTheory.UnipCT.topFacts σ G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.W.J
  haveI : MeasurableMul (UA σ G.W.J) := inferInstance
  haveI : MeasurableConstSMul (ratU σ G.W.J) (UA σ G.W.J) :=
    ⟨fun γ => (measurable_const_mul (γ.1 : UA σ G.W.J))⟩
  haveI : SMulInvariantMeasure (ratU σ G.W.J) (UA σ G.W.J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  set f : UA σ G.W.J → ℂ := fun x => G.M'.I om' Φ x * starRingEnd ℂ (G.M'.I om' Ψ x) with hf
  have hmp : MeasurePreserving (· * h) μ μ := ⟨measurable_mul_const h, hR⟩
  have hemb : MeasurableEmbedding (· * h : UA σ G.W.J → UA σ G.W.J) := (MeasurableEquiv.mulRight h).measurableEmbedding
  have h𝓕' : IsFundamentalDomain (ratU σ G.W.J) ((· * h) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : ratU σ G.W.J) (x : UA σ G.W.J), f (γ • x * h) = f (x * h) := by
    intro γ x
    simp only [hf, Subgroup.smul_def, smul_eq_mul, mul_assoc]
    rw [inv Φ hΦ γ.1 γ.2, inv Ψ hΨ γ.1 γ.2]
  calc ∫ x in 𝓕, f (x * h) ∂μ = ∫ x in (· * h) ⁻¹' 𝓕, f (x * h) ∂μ := h𝓕.setIntegral_eq h𝓕' hinv
    _ = ∫ y in 𝓕, f y ∂μ := hmp.setIntegral_preimage_emb hemb f 𝓕

end GlobalTheory.ThKRightInv
