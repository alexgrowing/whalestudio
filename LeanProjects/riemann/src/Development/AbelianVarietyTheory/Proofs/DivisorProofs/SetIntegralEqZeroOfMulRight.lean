import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoPhase

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phase (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (w : Fin d₁ → E) (u : UA σ W.J) : AF F :=
  -Algebra.trace (AF F) (AE F E) (GlobalTheory.UnipMass.hA σ W.J (incV F (H'.ι *ᵥ w)) (mat u⁻¹ *ᵥ incV F H'.y))

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in

theorem setIntegral_eq_zero_of_mul_right (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁)
    (μ : Measure (unip σ W H')) [hμ : μ.IsHaarMeasure] (𝓕 : Set (unip σ W H'))
    (h𝓕 : IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ) (h1 : μ 𝓕 = 1)
    (f : unip σ W H' → ℂ) (hf : ∀ γ ∈ (ratU σ W.J).subgroupOf (unip σ W H'), ∀ x, f (γ * x) = f x)
    (g : unip σ W H') (t : ℂ) (ht : t ≠ 1) (hg : ∀ x, f (x * g) = t * f x) : ∫ x in 𝓕, f x ∂μ = 0 := by
  obtain ⟨htg, hlc, hsc, ht2⟩ := GlobalTheory.UnipCT.topFacts σ W.J
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ W H') :=
    (GlobalTheory.UnipCT.isClosed_unip σ W H').isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := GlobalTheory.UnipCT.countable_ratU (F := F) (σ := σ) W.J
  set Γ := (ratU σ W.J).subgroupOf (unip σ W H') with hΓ
  haveI : Countable Γ :=
    Function.Injective.countable (f := fun γ : Γ => (⟨γ.1.1, γ.2⟩ : ratU σ W.J))
      fun a b hab => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hab
  haveI : MeasurableMul (unip σ W H') := inferInstance
  haveI : SigmaCompactSpace (unip σ W H') := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : MeasurableConstSMul Γ (unip σ W H') := ⟨fun γ => measurable_const_mul (γ.1 : unip σ W H')⟩
  haveI : SMulInvariantMeasure Γ (unip σ W H') μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  haveI : (μ.map (· * g)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ g
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  set c := Measure.haarScalarFactor (μ.map (· * g)) μ
  have h𝓕' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) (e := id) Function.bijective_id ?_
    intro γ x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := h𝓕'.measure_eq h𝓕
  have hmap : (μ.map (· * g)) 𝓕 = μ ((· * g) ⁻¹' 𝓕) := MeasurableEquiv.map_apply (MeasurableEquiv.mulRight g) 𝓕
  have hc1 : c = 1 := by
    have e1 : (c : ENNReal) * μ 𝓕 = 1 * μ 𝓕 := by
      calc (c : ENNReal) * μ 𝓕 = (c • μ) 𝓕 := by simp [Measure.smul_apply]
        _ = (μ.map (· * g)) 𝓕 := by rw [← hc]
        _ = 1 * μ 𝓕 := by rw [one_mul]; exact hmap.trans hm
    rw [h1, mul_one, one_mul] at e1
    exact_mod_cast e1
  have hR : μ.map (· * g) = μ := by rw [hc, hc1, one_smul]
  have hmp : MeasurePreserving (· * g) μ μ := ⟨measurable_mul_const g, hR⟩
  have hemb : MeasurableEmbedding (· * g : unip σ W H' → unip σ W H') :=
    (MeasurableEquiv.mulRight g).measurableEmbedding
  have hinv : ∀ (γ : Γ) (x : unip σ W H'), f (γ • x * g) = f (x * g) := by
    intro γ x
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ.1 γ.2 _
  have key : ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ :=
    (h𝓕.setIntegral_eq h𝓕' hinv).trans (hmp.setIntegral_preimage_emb hemb f 𝓕)
  have e2 : ∫ x in 𝓕, f (x * g) ∂μ = t * ∫ x in 𝓕, f x ∂μ := by
    simp_rw [hg]; exact integral_const_mul _ _
  have e3 : (t - 1) * ∫ x in 𝓕, f x ∂μ = 0 := by rw [sub_mul, ← e2, key, one_mul, sub_self]
  exact (mul_eq_zero.1 e3).resolve_left (sub_ne_zero.2 ht)

end GlobalTheory.IsoPhase
