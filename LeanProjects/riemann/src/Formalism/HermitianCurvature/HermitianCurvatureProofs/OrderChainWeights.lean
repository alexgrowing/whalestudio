import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.OrderChainWeights

open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3
open scoped ENNReal

theorem mem_ROrd {o : Type} [CommRing o] [IsLocalRing o] (p : o × o) :
    p ∈ ROrd o ↔ IsLocalRing.residue o p.1 = IsLocalRing.residue o p.2 := by
  unfold ROrd
  rw [RingHom.mem_eqLocus]
  rfl

theorem chainWeight_snoc {X : Type} (nrm : X → ℝ≥0∞) (i : ℕ) (h : Fin i → X) (c : X) :
    chainWeight nrm (i + 1) (Fin.snoc h c : Fin (i + 1) → X) =
      chainWeight nrm i h * (∏ l, nrm (h l)) ^ 2 := by
  unfold chainWeight
  rw [Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    have hl' : l < i := Finset.mem_range.mp hl
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc, Fin.val_last]
    rw [if_neg (by omega), mul_one]
  · rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc, Fin.val_last, lt_irrefl, if_false, mul_one,
      Fin.is_lt, if_true]
    rw [Finset.prod_pow]

theorem measurable_chainWeight {X : Type} [MeasurableSpace X] (nrm : X → ℝ≥0∞) (hn : Measurable nrm)
    (i : ℕ) : Measurable (chainWeight nrm i) := by
  unfold chainWeight
  refine Finset.measurable_prod _ fun l _ => Finset.measurable_prod _ fun j _ => ?_
  by_cases hjl : (j : ℕ) < l
  · simp only [hjl, if_true]
    exact (hn.comp (measurable_pi_apply j)).pow_const 2
  · simp only [hjl, if_false]
    exact measurable_const

theorem ae_pi_all {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (i : ℕ)
    (p : X → Prop) (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ h ∂(Measure.pi fun _ : Fin i => μ), ∀ l, p (h l) := by
  rw [ae_all_iff]
  intro l
  exact Measure.tendsto_eval_ae_ae.eventually hp

end Formalism.FourierDecayAlt.P.OrderChainWeights

namespace Formalism.FourierDecayAlt.P

open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.OrderChainWeights
open scoped ENNReal

theorem order_unit_group : Formalism.FourierDecayAlt.S3.ROrderUnits := by
  intro o _ _
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun k => ?_⟩
  · have h1 : IsUnit ((x : o × o).1) := (hx.map (ROrd o).subtype).map (RingHom.fst o o)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr h1
  · have hm := (mem_ROrd (x : o × o)).mp x.2
    obtain ⟨a, ha⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hx
    obtain ⟨b, hb⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (hm ▸ hx)
    have hinv : ((↑a⁻¹ : o), (↑b⁻¹ : o)) ∈ ROrd o := by
      rw [mem_ROrd]
      simp only [map_units_inv, ha, hb, hm]
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x : o × o).1 * ↑a⁻¹ = 1
      rw [← ha]
      exact a.mul_inv
    · show (x : o × o).2 * ↑b⁻¹ = 1
      rw [← hb]
      exact b.mul_inv
  · obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective k
    exact ⟨⟨(a, a), (mem_ROrd _).mpr rfl⟩, ha⟩

theorem rOrderSelfDual_statement : Formalism.FourierDecayAlt.S3.ROrderSelfDual := by
  intro o _ _ _ k0 _ _ _ ϖ hϖ a₁ a₂
  have hinj : Function.Injective (algebraMap o k0) := IsFractionRing.injective o k0
  have hϖ0 : algebraMap o k0 ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    exact hϖ.ne_zero
  have hmax : IsLocalRing.maximalIdeal o = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hres0 : IsLocalRing.residue o ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self ϖ
  constructor
  · intro h
    obtain ⟨y1, hy1⟩ := h ⟨(ϖ, 0), (mem_ROrd _).mpr (by simp [hres0])⟩
    obtain ⟨y2, hy2⟩ := h ⟨(0, ϖ), (mem_ROrd _).mpr (by simp [hres0])⟩
    obtain ⟨y3, hy3⟩ := h ⟨(1, 1), (mem_ROrd _).mpr rfl⟩
    have e1 : algebraMap o k0 y1 = a₁ := by
      rw [hy1]
      dsimp only
      rw [map_zero, mul_zero, sub_zero]
      field_simp
    have e2 : algebraMap o k0 y2 = -a₂ := by
      rw [hy2]
      dsimp only
      rw [map_zero, mul_zero, zero_sub]
      field_simp
    have e3 : algebraMap o k0 y3 = (a₁ - a₂) / algebraMap o k0 ϖ := by
      rw [hy3]
      dsimp only
      rw [map_one, mul_one, mul_one]
    have hd : y1 + y2 = ϖ * y3 := by
      apply hinj
      rw [map_add, map_mul, e1, e2, e3]
      field_simp
      try ring
    refine ⟨⟨(y1, -y2), (mem_ROrd _).mpr ?_⟩, e1, ?_⟩
    · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]
      exact ⟨y3, by rw [sub_neg_eq_add, hd]⟩
    · show algebraMap o k0 (-y2) = a₂
      rw [map_neg, e2, neg_neg]
  · rintro ⟨x, hx1, hx2⟩ b
    have hm := (mem_ROrd (x : o × o)).mp x.2
    have hb := (mem_ROrd (b : o × o)).mp b.2
    have hmem : (x : o × o).1 * (b : o × o).1 - (x : o × o).2 * (b : o × o).2 ∈ Ideal.span {ϖ} := by
      rw [← hmax, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, map_mul, hm, hb, sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨y, ?_⟩
    rw [← hx1, ← hx2, eq_div_iff hϖ0, ← map_mul, ← map_mul, ← map_mul, ← map_sub, hy]

theorem chain_weight_identity : Formalism.FourierDecayAlt.S3.ChainIdentity := by
  intro X _ μ _ nrm Kk hn hK hae h0 hstep i
  induction i with
  | zero =>
    have hw : ∀ c : Fin 0 → X, chainWeight nrm 0 c = 1 := fun c => by simp [chainWeight]
    simp only [h0, hw, one_mul, lintegral_const, Measure.pi_univ, Finset.univ_eq_empty,
      Finset.prod_empty]
  | succ i ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (i + 1) => X) (Fin.last i) with he
    have hmp : MeasurePreserving e.symm (μ.prod (Measure.pi fun _ : Fin i => μ))
        (Measure.pi fun _ : Fin (i + 1) => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (i + 1) => μ) (Fin.last i)).symm e
    rw [← hmp.lintegral_comp_emb e.symm.measurableEmbedding]
    have hFm : Measurable fun z : X × (Fin i → X) =>
        Kk (i + 1) (e.symm z) * chainWeight nrm (i + 1) (e.symm z) :=
      ((hK (i + 1)).comp e.symm.measurable).mul ((measurable_chainWeight nrm hn (i + 1)).comp e.symm.measurable)
    rw [lintegral_prod_symm _ hFm.aemeasurable]
    have hsn : ∀ (h : Fin i → X) (c : X), e.symm (c, h) = (Fin.snoc h c : Fin (i + 1) → X) := by
      intro h c
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_last' c h
    simp_rw [hsn, chainWeight_snoc]
    rw [← ih]
    apply lintegral_congr_ae
    filter_upwards [ae_pi_all μ i _ hae] with h hh
    have hmeas : Measurable fun c : X => Kk (i + 1) (Fin.snoc h c : Fin (i + 1) → X) := by
      have h1 : Measurable fun c : X => e.symm (c, h) :=
        e.symm.measurable.comp (measurable_id.prodMk measurable_const)
      simp_rw [hsn] at h1
      exact (hK (i + 1)).comp h1
    rw [lintegral_mul_const _ hmeas, hstep i h hh]
    have hP0 : (∏ l, nrm (h l)) ^ 2 ≠ 0 :=
      pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun l _ => (hh l).1)
    have hPt : (∏ l, nrm (h l)) ^ 2 ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.prod_ne_top fun l _ => (hh l).2)
    calc ((∏ l, nrm (h l)) ^ 2)⁻¹ * Kk i h * (chainWeight nrm i h * (∏ l, nrm (h l)) ^ 2)
        = Kk i h * chainWeight nrm i h * (((∏ l, nrm (h l)) ^ 2)⁻¹ * (∏ l, nrm (h l)) ^ 2) := by ring
      _ = Kk i h * chainWeight nrm i h := by rw [ENNReal.inv_mul_cancel hP0 hPt, mul_one]

theorem unitHeadsMass_statement : Formalism.FourierDecayAlt.S3.UnitHeadsMass := by
  intro X _ μ _ nrm Kk Rs Ru r hRs hRu hnrm hae hK
  set A := {c : Fin (r + 1) → X | ∀ l : Fin (r + 1), (l : ℕ) < r → c l ∈ Ru} with hAdef
  set B : Set (Fin (r + 1) → X) := Set.univ.pi fun l : Fin (r + 1) => if (l : ℕ) < r then Ru else Rs
    with hBdef
  have hBm : MeasurableSet B := by
    refine MeasurableSet.univ_pi fun l => ?_
    split_ifs
    · exact hRu
    · exact hRs
  have hBA : B ⊆ A := by
    intro c hc l hl
    have := hc l (Set.mem_univ _)
    simpa [hl] using this
  have hcongr : ∀ᵐ c ∂((Measure.pi fun _ : Fin (r + 1) => μ).restrict A),
      Kk (r + 1) c * chainWeight nrm (r + 1) c = B.indicator 1 c := by
    have hA : ∀ᵐ c ∂((Measure.pi fun _ : Fin (r + 1) => μ).restrict A), c ∈ A := by
      rw [ae_restrict_iff']
      · exact Filter.Eventually.of_forall fun c hc => hc
      · have : A = ⋂ l : Fin (r + 1), {c : Fin (r + 1) → X | (l : ℕ) < r → c l ∈ Ru} := by
          ext c
          simp [hAdef]
        rw [this]
        refine MeasurableSet.iInter fun l => ?_
        by_cases hl : (l : ℕ) < r
        · simp only [hl, true_implies]
          exact measurable_pi_apply l hRu
        · simp only [hl, false_implies, Set.setOf_true]
          exact MeasurableSet.univ
    filter_upwards [hA, ae_restrict_of_ae (ae_pi_all μ (r + 1) _ hae)] with c hcA hc0
    rw [hK c hcA (hc0 _)]
    have hw : chainWeight nrm (r + 1) c = 1 := by
      unfold chainWeight
      refine Finset.prod_eq_one fun l hl => Finset.prod_eq_one fun j _ => ?_
      split_ifs with hjl
      · have hl' := Finset.mem_range.mp hl
        rw [hnrm _ (hcA j (by omega)), one_pow]
      · rfl
    rw [hw, mul_one]
    by_cases hs : c (Fin.last r) ∈ Rs
    · have hcB : c ∈ B := by
        intro l _
        by_cases hl : (l : ℕ) < r
        · simp only [hl, if_true]
          exact hcA l hl
        · have hle : l = Fin.last r := Fin.ext (by have := l.is_lt; simp; omega)
          subst hle
          simpa using hs
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hcB]
      simp
    · have hcB : c ∉ B := by
        intro hmem
        apply hs
        have := hmem (Fin.last r) (Set.mem_univ _)
        simpa using this
      rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hcB]
  rw [lintegral_congr_ae hcongr, lintegral_indicator_one hBm, Measure.restrict_apply hBm,
    Set.inter_eq_left.mpr hBA, Measure.pi_pi, Fin.prod_univ_castSucc]
  simp [Finset.prod_const]

end Formalism.FourierDecayAlt.P
