import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LintegralFintypeProd

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK

section Pi

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)]

theorem isGrp_pi (K : ∀ v, Set (G v)) (hK : ∀ v, IsGrp (K v)) : IsGrp (Set.pi univ K) := by
  refine ⟨fun v _ => (hK v).1, fun a ha b hb v _ => (hK v).2.1 _ (ha v trivial) _ (hb v trivial),
    fun a ha v _ => (hK v).2.2 _ (ha v trivial)⟩

theorem invOn_pi (K : ∀ v, Set (G v)) (μ : ∀ v, Measure (G v)) (h : ∀ v, InvOn (μ v) (K v)) :
    InvOn (Measure.pi μ) (Set.pi univ K) := by
  haveI : ∀ v, SigmaFinite (μ v) := fun v => (h v).1
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun m : Measure (∀ v, G v) => m univ) h0
    simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and] at h1
    obtain ⟨v, hv⟩ := h1
    exact (h v).2.1 (Measure.measure_univ_eq_zero.1 hv)
  · have e : (Set.pi univ K)ᶜ = ⋃ v, (fun x : (∀ v, G v) => x v) ⁻¹' (K v)ᶜ := by
      ext x
      simp [Set.mem_pi]
    rw [e]
    exact measure_iUnion_null fun v => Measure.pi_eval_preimage_null μ ((h v).2.2.1)
  · intro s hs
    have hmap : ∀ v, (μ v).map (fun x => s v * x) = μ v := fun v => (h v).2.2.2 (s v) (hs v trivial)
    haveI : ∀ v, SigmaFinite ((μ v).map (fun x => s v * x)) := fun v => by
      rw [hmap v]
      infer_instance
    have e : (fun x : (∀ v, G v) => s * x) = fun x v => (fun y => s v * y) (x v) := rfl
    rw [e, Measure.pi_map_pi (fun v => (measurable_const_mul (s v)).aemeasurable)]
    simp only [hmap]

theorem lintegral_pi_prod_mul (μ ν : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] (φ : ∀ v, G v → ℝ≥0∞) (hφ : ∀ v, Measurable (φ v)) :
    ∫⁻ p, ∏ v, φ v (p.1 v * p.2 v) ∂((Measure.pi μ).prod (Measure.pi ν)) =
      ∏ v, ∫⁻ s, φ v s ∂(mulMap (μ v) (ν v)) := by
  have hm : Measurable (fun p : (∀ v, G v) × (∀ v, G v) => ∏ v, φ v (p.1 v * p.2 v)) :=
    Finset.measurable_prod _ fun v _ => (hφ v).comp
      (((measurable_pi_apply v).comp measurable_fst).mul ((measurable_pi_apply v).comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  have hin : ∀ x : (∀ v, G v), ∫⁻ y, ∏ v, φ v (x v * y v) ∂(Measure.pi ν) =
      ∏ v, ∫⁻ y, φ v (x v * y) ∂(ν v) := fun x =>
    lintegral_fintype_prod (fun v y => φ v (x v * y)) (fun v => (hφ v).comp (measurable_const_mul _))
  simp_rw [hin]
  rw [lintegral_fintype_prod (fun v x => ∫⁻ y, φ v (x * y) ∂(ν v))
    (fun v => ((hφ v).comp measurable_mul).lintegral_prod_right')]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [mulMap, lintegral_map (hφ v) measurable_mul,
    lintegral_prod (f := fun z : G v × G v => φ v (z.1 * z.2))
      (show Measurable (fun z : G v × G v => φ v (z.1 * z.2)) from
        (hφ v).comp measurable_mul).aemeasurable]

end Pi

theorem weil_quotient_global_assumptions : GlobAsm := by
  intro hU hL ι _ n ε N H hNc hHc hNg hHg hnorm hunim muN muH nuQ hmuN hmuH hW
  have hloc := fun v => hL (Formalism.REAL.UJ (ε v)) (Formalism.REAL.muG (ε v)) (N v) (H v) (hNc v) (hHc v)
    (hNg v) (hHg v) (hnorm v) (hunim v)
  choose μN μH β hμN hμH hμS hβm hβ1 hLW using hloc
  haveI := fun v => (hμN v).1
  haveI := fun v => (hμH v).1
  haveI := fun v => (hμS v).1
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := hU (∀ v, Formalism.REAL.UJ (ε v)) (Set.pi univ N)
    (isClosed_set_pi fun v _ => hNc v) (isGrp_pi N hNg) muN (Measure.pi μN) hmuN
    (invOn_pi N μN hμN)
  obtain ⟨cH, hcH0, hcHt, hcH⟩ := hU (∀ v, Formalism.REAL.UJ (ε v)) (Set.pi univ H)
    (isClosed_set_pi fun v _ => (hHc v).isClosed) (isGrp_pi H hHg) muH (Measure.pi μH) hmuH
    (invOn_pi H μH hμH)
  refine ⟨fun v => mulMap (μN v) (μH v), fun v => (Formalism.REAL.muG (ε v)).withDensity (β v),
    (cN * cH)⁻¹, ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top hcNt hcHt),
    ENNReal.inv_ne_top.mpr (mul_ne_zero hcN0 hcH0), fun v => ⟨hμS v, hLW v⟩, ?_⟩
  intro F hFm hFinv
  set f : (∀ v, Formalism.REAL.UJ (ε v)) → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hfdef
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := hW f hfm

  have hL1 : ∫⁻ x, f x ∂(Measure.pi fun v => Formalism.REAL.muG (ε v)) =
      ∏ v, ∫⁻ y, F v y ∂((Formalism.REAL.muG (ε v)).withDensity (β v)) := by
    rw [hfdef, lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [lintegral_withDensity_eq_lintegral_mul _ (hβm v) (hFm v)]
    rfl

  have hin : ∀ x, ∫⁻ s, f (s * x) ∂((muN.prod muH).map (fun p => p.1 * p.2)) =
      (cN * cH) * ∏ v, F v (x v) := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      hcN, hcH,
      Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have h1 : ∀ p : (∀ v, Formalism.REAL.UJ (ε v)) × (∀ v, Formalism.REAL.UJ (ε v)),
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [h1]
    rw [lintegral_pi_prod_mul μN μH (fun v z => β v (z * x v) * F v (z * x v)) (fun v => ((hβm v).comp (measurable_mul_const _)).mul
      ((hFm v).comp (measurable_mul_const _)))]
    have h2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(mulMap (μN v) (μH v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(mulMap (μN v) (μH v)), s ∈ prodSet (N v) (H v) :=
        mem_ae_iff.mpr (hμS v).2.2.1
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        simp only [hFinv v m hm h hh])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [h2]
    ring
  simp_rw [hin] at key
  have hPm : Measurable (fun x : (∀ v, Formalism.REAL.UJ (ε v)) => ∏ v, F v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hFm v).comp (measurable_pi_apply v)
  rw [lintegral_const_mul _ hPm, hL1] at key
  change _ = (cN * cH)⁻¹ * ∏ v, ∫⁻ y, F v y ∂((Formalism.REAL.muG (ε v)).withDensity (β v))
  rw [key, ← mul_assoc, ENNReal.inv_mul_cancel (mul_ne_zero hcN0 hcH0)
    (ENNReal.mul_ne_top hcNt hcHt), one_mul]

end QPK
