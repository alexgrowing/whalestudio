import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ESSymmApply

noncomputable section

namespace PI.VolStabS.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]

instance Rm_sf (S : Finset ι) : SigmaFinite (Rm m L S) := by unfold Rm; infer_instance

lemma Qm_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun z => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j)) (Qm m L S) ∧
    ∫ z, ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j) ∂Qm m L S =
      (∏ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  by_cases h : ∀ i ∉ S, m i (L i) ≠ 0 ∧ m i (L i) ≠ ∞
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (h i.1 i.2)
    have hQ : Qm m L S = tl m L S • Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1) := by
      unfold Qm
      rw [dif_pos h]
    set J := T.subtype (fun i => i ∉ S) with hJ
    have hgP : ∀ j : J, Integrable (g j.1.1) (Pn m L j.1.1) := by
      intro j
      exact ((hg _).restrict).smul_measure (ENNReal.inv_ne_top.mpr (h _ j.1.2).1)
    have hF : Integrable (fun y : (j : J) → W j.1.1 => ∏ j : J, g j.1.1 (y j))
        (Measure.pi fun j : J => Pn m L j.1.1) := Integrable.fintype_prod_dep hgP
    have hmap : (Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)).map J.restrict
        = Measure.pi fun j : J => Pn m L j.1.1 := Measure.infinitePi_map_restrict _
    have hfun : (fun z : (i : {i // i ∉ S}) → W i.1 => ∏ j ∈ J, g j.1 (z j))
        = (fun y : (j : J) → W j.1.1 => ∏ j : J, g j.1.1 (y j)) ∘ J.restrict := by
      funext z
      simp only [Function.comp_apply, Finset.restrict]
      exact (Finset.prod_coe_sort J (fun j => g j.1 (z j))).symm
    have hmeas : AEMeasurable (J.restrict : ((i : {i // i ∉ S}) → W i.1) → _)
        (Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)) :=
      (Finset.measurable_restrict J).aemeasurable
    have hF' := hF
    rw [← hmap] at hF'
    have hint : Integrable (fun z : (i : {i // i ∉ S}) → W i.1 => ∏ j ∈ J, g j.1 (z j))
        (Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)) := by
      rw [hfun]
      exact (integrable_map_measure hF'.aestronglyMeasurable hmeas).mp hF'
    have hI : ∫ z, ∏ j ∈ J, g j.1 (z j) ∂(Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1))
        = ∫ y, ∏ j : J, g j.1.1 (y j) ∂(Measure.pi fun j : J => Pn m L j.1.1) := by
      rw [hfun, ← hmap]
      exact (integral_map hmeas hF'.aestronglyMeasurable).symm
    refine ⟨by rw [hQ]; exact hint.smul_measure_nnreal, ?_⟩
    have hJprod : ∀ f : ι → ℂ, ∏ j : J, f j.1.1 = ∏ i ∈ T \ S, f i := by
      intro f
      rw [Finset.prod_coe_sort J (fun j => f j.1), Finset.sdiff_eq_filter, ← Finset.subtype_map]
      exact (Finset.prod_subtype_map_embedding (fun _ _ => rfl)).symm
    have key : ∀ i ∈ T \ S, ((am m L i : ℝ) : ℂ) * ∫ w, g i w ∂(Pn m L i)
        = ∫ w, g i w ∂(mu m L S i) := by
      intro i hi
      have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
      obtain ⟨h0, htop⟩ := h i hiS
      have hone : ((am m L i : ℝ) : ℂ) * (((m i (L i))⁻¹).toReal : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, am, ENNReal.coe_toNNReal_eq_toReal, ← ENNReal.toReal_mul,
          ENNReal.mul_inv_cancel h0 htop, ENNReal.toReal_one, Complex.ofReal_one]
      rw [show Pn m L i = (m i (L i))⁻¹ • (m i).restrict (L i) from rfl,
        show mu m L S i = (m i).restrict (L i) by simp [mu, hiS],
        integral_smul_measure, Complex.real_smul, ← mul_assoc, hone, one_mul]
    rw [hQ, integral_smul_nnreal_measure, hI, integral_fintype_prod_eq_prod]
    rw [hJprod (fun i => ∫ w, g i w ∂(Pn m L i))]
    rw [tl_split hT hST, NNReal.smul_def, Complex.real_smul, NNReal.coe_mul, NNReal.coe_prod,
      Complex.ofReal_mul, Complex.ofReal_prod, ← Finset.prod_congr rfl key, Finset.prod_mul_distrib]
    ring
  · have hQ : Qm m L S = 0 := by
      unfold Qm
      rw [dif_neg h]
    rw [hQ]
    refine ⟨integrable_zero_measure, ?_⟩
    rw [integral_zero_measure]
    push_neg at h
    obtain ⟨i, hiS, hi⟩ := h
    have h0 : m i (L i) = 0 := by
      by_contra h0
      exact hfin i (hi h0)
    by_cases hiT : i ∈ T
    · rw [Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.mpr ⟨hiT, hiS⟩)]
      · simp
      · have hz : mu m L S i = 0 := by simp [mu, hiS, Measure.restrict_eq_zero.mpr h0]
        rw [hz, integral_zero_measure]
    · rw [tl_zero hT hiT (by simp [am, h0])]
      simp

lemma kap_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun x => ∏ i ∈ T, g i (x i)) (kap m L S) ∧
    ∫ x, ∏ i ∈ T, g i (x i) ∂kap m L S =
      (∏ i ∈ T, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  obtain ⟨hQi, hQe⟩ := Qm_integral hfin hT hST g hg
  have hRi : Integrable (fun p : (j : S) → W j.1 => ∏ j : S, g j.1 (p j)) (Rm m L S) := by
    unfold Rm
    exact Integrable.fintype_prod_dep (fun j => (hg j.1).restrict)
  have hRe : ∫ p, ∏ j : S, g j.1 (p j) ∂(Rm m L S) = ∏ i ∈ S, ∫ w, g i w ∂(mu m L S i) := by
    unfold Rm
    rw [integral_fintype_prod_eq_prod, ← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp [mu, j.2]
  have hfun : (fun x : (i : ι) → W i => ∏ i ∈ T, g i (x i)) ∘ (eS S).symm
      = fun z => (∏ j : S, g j.1 (z.1 j)) * ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z.2 j) := by
    funext z
    simp only [Function.comp_apply]
    rw [← Finset.prod_sdiff hST]
    refine (mul_comm _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [eS_symm_apply, dif_pos j.2]
    · rw [Finset.sdiff_eq_filter, ← Finset.subtype_map]
      refine Finset.prod_subtype_map_embedding (fun j _ => ?_)
      rw [eS_symm_apply, dif_neg j.2]
  have hprod := hRi.mul_prod hQi
  refine ⟨?_, ?_⟩
  · unfold kap
    rw [integrable_map_equiv, hfun]
    exact hprod
  · unfold kap
    rw [integral_map_equiv]
    rw [show (fun z => ∏ i ∈ T, g i ((eS S).symm z i))
        = fun z => (∏ j : S, g j.1 (z.1 j)) * ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z.2 j)
        from hfun]
    rw [integral_prod_mul (f := fun p : (j : S) → W j.1 => ∏ j : S, g j.1 (p j))
      (g := fun q : (i : {i // i ∉ S}) → W i.1 => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (q j))]
    rw [hRe, hQe, ← mul_assoc, mul_comm (∏ i ∈ S, _), Finset.prod_sdiff hST]

end PI.VolStabS.RPA
