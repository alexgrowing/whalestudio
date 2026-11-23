import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.ColumnAdditionFixesTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.IsTopRingTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.RightKDef

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct

def OmHyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E))
    (T T' : F) (κ : HA (Fv F v) σ J) (μG : Measure (HA (Fv F v) σ J))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (μS0' : Measure (S0 (Fv F v) σ J P')) : Prop :=
  StdHyp σ J ψ ∧ P.IsStd σ J T ∧ P'.IsStd σ J T' ∧ IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧
    g.Prime ∧ (g : 𝓞 F) ∈ v.asIdeal ∧ Ideal.absNorm v.asIdeal = g ∧ etaV (E := E) v = 1 ∧
    κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ∧
    (∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (κ • ratTup (Fv F v) (F0 P')) a - locF v (ratTup (Fv F v) (F0 P)) a =
        sc (E := E) v (g : Fv F v) • y) ∧
    μG.IsHaarMeasure ∧
    μS0.IsHaarMeasure ∧ IsCompatLoc σ J v (F0 P) μG μS0 (omAt σ J ψ v (TFl σ J v P)) ∧
    μS0'.IsHaarMeasure ∧ IsCompatLoc σ J v (F0 P') μG μS0' (omAt σ J ψ v (TFl σ J v P')) ∧
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) ∧ IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P'))) ∧
    LocMassOrdW.IsLatLoc v Λ ∧ (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 ∧ (μS0' (stabilizerCompact σ J v Λ P')).toReal ≠ 0

def OmMeas : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E))
    (T T' : F) (κ : HA (Fv F v) σ J) (μG : Measure (HA (Fv F v) σ J))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (μS0' : Measure (S0 (Fv F v) σ J P')),
    OmHyp σ J ψ v g P P' Λ T T' κ μG μS0 μS0' →
    MeasurableSet (OmTyp v Λ g r) ∧ MeasurableSet (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ∧
      MeasurableSet (K1 σ J v Λ g P) ∧
      MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) (F0 P)) ''
        Formalism.L2.SG.TypedSets.Kv σ J Λ v) ∧
      ∀ k : HA (Fv F v) σ J, MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) (F0 P')) ''
        {c | k⁻¹ * c * κ⁻¹ ∈ K1 σ J v Λ g P})

theorem weil_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) {a : ℕ}
    (X0 : Fin a → Fin n → E) (μG : Measure (HA (Fv F v) σ J))
    (μ' : Measure (stabT (Fv F v) σ J X0)) (ν : Measure (TupV (E := E) v n a))
    (hc : IsCompatLoc σ J v X0 μG μ' ν) (C : Set (HA (Fv F v) σ J)) (hCm : MeasurableSet C)
    (D : Set (stabT (Fv F v) σ J X0)) (hDm : MeasurableSet D)
    (hCD : ∀ c ∈ C, ∀ h : stabT (Fv F v) σ J X0, c * (h : HA (Fv F v) σ J) ∈ C ↔ h ∈ D)
    (hAm : MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) X0) '' C)) :
    ν ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) X0) '' C) * μ' D = μG C := by
  classical
  set X0r := ratTup (F := F) (Fv F v) X0 with hX0r
  set A := (fun c : HA (Fv F v) σ J => c • X0r) '' C with hAdef
  let s : TupV (E := E) v n a → HA (Fv F v) σ J := fun Y =>
    if hY : Y ∈ A then hY.choose else if h' : ∃ g : HA (Fv F v) σ J, g • X0r = Y then h'.choose else 1
  have hs : ∀ Y, (∃ g : HA (Fv F v) σ J, g • X0r = Y) → s Y • X0r = Y := by
    intro Y hY
    by_cases hA : Y ∈ A
    · simp only [s, dif_pos hA]; exact hA.choose_spec.2
    · simp only [s, dif_neg hA, dif_pos hY]; exact hY.choose_spec
  have hf : Measurable (C.indicator (1 : HA (Fv F v) σ J → ENNReal)) := measurable_one.indicator hCm
  have key := hc.2 _ hf s hs
  have hL : ∫⁻ g, C.indicator (1 : HA (Fv F v) σ J → ENNReal) g ∂μG = μG C := lintegral_indicator_one hCm
  have hpt : ∀ Y, (∃ g : HA (Fv F v) σ J, g • X0r = Y) →
      ∫⁻ h', C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) ∂μ' =
        A.indicator (fun _ => μ' D) Y := by
    intro Y hY
    by_cases hA : Y ∈ A
    · rw [Set.indicator_of_mem hA]
      have hk : hA.choose ∈ C := hA.choose_spec.1
      have hsY : s Y = hA.choose := by simp only [s, dif_pos hA]
      rw [← lintegral_indicator_one hDm]
      congr 1
      funext h'
      rw [hsY]
      by_cases hh : h' ∈ D
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hCD _ hk h').2 hh)]; rfl
      · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (fun hm => hh ((hCD _ hk h').1 hm))]
    · rw [Set.indicator_of_notMem hA]
      have hz : ∀ h' : stabT (Fv F v) σ J X0,
          C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) = 0 := by
        intro h'
        rw [Set.indicator_of_notMem]
        intro hmem
        apply hA
        refine ⟨s Y * (h' : HA (Fv F v) σ J), hmem, ?_⟩
        have hst : (h' : HA (Fv F v) σ J) • X0r = X0r := h'.2
        show (s Y * (h' : HA (Fv F v) σ J)) • X0r = Y
        rw [mul_smul, hst, hs Y hY]
      simp [hz]
  have hae : ∀ᵐ Y ∂ν, ∃ g : HA (Fv F v) σ J, g • X0r = Y := ae_iff.mpr hc.1
  have hR' : ∫⁻ Y, ∫⁻ h', C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) ∂μ' ∂ν =
      ∫⁻ Y, A.indicator (fun _ => μ' D) Y ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hae] with Y hY
    exact hpt Y hY
  rw [hL, hR', lintegral_indicator_const hAm] at key
  rw [key, mul_comm]

theorem stepOm_ofK (hW : StepW) (hM : OmMeas) (hRK : RightK) (hO : LocMassOrdW.OmSF) :
    StepOm := by
  intro F E _ _ _ _ _ σ n J ψ v r g P P' Λ T T' κ μG μS0 μS0' hStd hP hP' hSD hUn hg hgv hN hEta hκ
    hκc hμG hμS0 hC hμS0' hC' hPr hPr' hL ha ha'
  have hH : OmHyp σ J ψ v g P P' Λ T T' κ μG μS0 μS0' :=
    ⟨hStd, hP, hP', hSD, hUn, hg, hgv, hN, hEta, hκ, hκc, hμG, hμS0, hC, hμS0', hC', hPr, hPr', hL, ha, ha'⟩
  obtain ⟨hOmm, hKm, hK1m, hAm, hBm⟩ := hM σ J ψ v g P P' Λ T T' κ μG μS0 μS0' hH
  have := hO σ J ψ v hStd (TFl σ J v P')
  set K := Formalism.L2.SG.TypedSets.Kv σ J Λ v with hKdef
  set K1s := K1 σ J v Λ g P with hK1def
  set X0r := ratTup (F := F) (Fv F v) (F0 P) with hX0r
  set X0r' := ratTup (F := F) (Fv F v) (F0 P') with hX0r'
  set ν := omAt σ J ψ v (TFl σ J v P) with hν
  set ν' := omAt σ J ψ v (TFl σ J v P') with hν'
  set a := μS0 (stabilizerCompact σ J v Λ P) with hadef
  set a' := μS0' (stabilizerCompact σ J v Λ P') with ha'def
  have hcg : CongL (Λ := Λ) g X0r (κ • X0r') := hκc
  have hS0Km : MeasurableSet (stabilizerCompact σ J v Λ P) := measurable_subtype_coe hKm
  have hS0Km' : MeasurableSet (stabilizerCompact σ J v Λ P') := measurable_subtype_coe hKm

  have hWK : ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * a = μG K := by
    refine weil_gen σ J v (F0 P) μG μS0 ν hC K hKm (stabilizerCompact σ J v Λ P) hS0Km ?_ hAm
    intro c hc h
    show c * (h : HA (Fv F v) σ J) ∈ K ↔ (h : HA (Fv F v) σ J) ∈ K
    constructor
    · intro hm
      have := kv_mul' (kv_inv' hc) hm
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · exact kv_mul' hc

  have hWC : ∀ k : HA (Fv F v) σ J,
      ν' ((fun c : HA (Fv F v) σ J => c • X0r') '' {c | k⁻¹ * c * κ⁻¹ ∈ K1s}) * a' = μG K1s := by
    intro k
    have hCm : MeasurableSet {c : HA (Fv F v) σ J | k⁻¹ * c * κ⁻¹ ∈ K1s} :=
      hK1m.preimage ((measurable_const_mul k⁻¹).mul_const κ⁻¹)
    refine (weil_gen σ J v (F0 P') μG μS0' ν' hC' _ hCm (stabilizerCompact σ J v Λ P') hS0Km' ?_ (hBm k)).trans ?_
    swap
    · show μG ((fun c => k⁻¹ * c) ⁻¹' ((fun c => c * κ⁻¹) ⁻¹' K1s)) = μG K1s
      rw [measure_preimage_mul]
      exact hRK σ J ψ v Λ μG hStd hSD hUn hEta hL hμG κ⁻¹ (kv_inv' hκ) K1s hK1m
    · intro c hc h
      show k⁻¹ * (c * (h : HA (Fv F v) σ J)) * κ⁻¹ ∈ K1s ↔ (h : HA (Fv F v) σ J) ∈ K
      rw [show k⁻¹ * (c * (h : HA (Fv F v) σ J)) * κ⁻¹ =
          (k⁻¹ * c * κ⁻¹) * (κ * (h : HA (Fv F v) σ J) * κ⁻¹) by group, congruence_mul_mem_iff hc]
      exact conj_mem_congruence_iff hκ hcg h.2
  have ha0' : a' ≠ 0 ∧ a' ≠ ⊤ := ⟨fun h => ha' (by rw [h]; rfl), fun h => ha' (by rw [h]; rfl)⟩
  have hWC' : ∀ k : HA (Fv F v) σ J,
      ν' ((fun c : HA (Fv F v) σ J => c • X0r') '' {c | k⁻¹ * c * κ⁻¹ ∈ K1s}) = μG K1s / a' := by
    intro k
    rw [ENNReal.eq_div_iff ha0'.1 ha0'.2, mul_comm]
    exact hWC k

  have hae' : ∀ᵐ Y ∂ν', ∃ g2 : HA (Fv F v) σ J, g2 • X0r' = Y := ae_iff.mpr hC'.1
  have hae : ∀ᵐ Y ∂ν, ∃ g1 : HA (Fv F v) σ J, g1 • X0r = Y := ae_iff.mpr hC.1
  have hslice : ∀ x, (∃ g1 : HA (Fv F v) σ J, g1 • X0r = x) →
      ν' (Prod.mk x ⁻¹' OmTyp v Λ g r) =
        ((fun c : HA (Fv F v) σ J => c • X0r) '' K).indicator (fun _ => μG K1s / a') x := by
    intro x ⟨g1, hg1⟩
    by_cases hx : x ∈ (fun c : HA (Fv F v) σ J => c • X0r) '' K
    · rw [Set.indicator_of_mem hx]
      obtain ⟨k, hk, hkx⟩ := hx
      rw [← hWC' k]
      apply measure_congr
      rw [Filter.eventuallyEq_set]
      filter_upwards [hae'] with x' hx'
      obtain ⟨g2, hg2⟩ := hx'
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨_, hp2, hcong⟩
        rw [← hg2] at hp2
        obtain ⟨k', hk', hk'x⟩ := hW σ J ψ v P' Λ T' hStd hP' hSD hUn hEta hPr' hL g2 hp2
        refine ⟨k', ⟨kv_mul' (kv_mul' (kv_inv' hk) hk') (kv_inv' hκ), ?_⟩, hk'x.trans hg2⟩
        have hc1 : CongL (Λ := Λ) g x x' := hcong
        have h1 := congL_smul (kv_inv' hk) hc1
        rw [← hkx, inv_smul_smul] at h1
        have h2 := congL_smul (kv_mul' (kv_mul' (kv_inv' hk) hk') (kv_inv' hκ)) hcg
        rw [show (k⁻¹ * k' * κ⁻¹) • κ • X0r' = k⁻¹ • x' by
          rw [← mul_smul, show k⁻¹ * k' * κ⁻¹ * κ = k⁻¹ * k' by group, mul_smul, hk'x, hg2]] at h2
        exact congL_trans h1 (congL_symm h2)
      · rintro ⟨c, homogComponent_comm_first_action, rfl⟩
        have hk1 := (mem_congruence_subgroup_iff).1 homogComponent_comm_first_action
        have hcK : c ∈ K := by
          have := kv_mul' (kv_mul' hk hk1.1) hκ
          rwa [show k * (k⁻¹ * c * κ⁻¹) * κ = c by group] at this
        refine ⟨?_, ?_, ?_⟩
        · rw [← hkx, locF_smul]; exact prim_smul hk hPr
        · rw [locF_smul]; exact prim_smul hcK hPr'
        · show CongL (Λ := Λ) g x (c • X0r')
          rw [← hkx, show c = k * ((k⁻¹ * c * κ⁻¹) * κ) by group, mul_smul]
          apply congL_smul hk
          rw [mul_smul]
          exact congL_trans hk1.2 (congL_smul hk1.1 hcg)
    · rw [Set.indicator_of_notMem hx]
      convert measure_empty (μ := ν')
      ext x'
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp1, _, _⟩
      rw [← hg1] at hp1
      obtain ⟨k, hk, hkx⟩ := hW σ J ψ v P Λ T hStd hP hSD hUn hEta hPr hL g1 hp1
      exact hx ⟨k, hk, hkx.trans hg1⟩
  have hprod : (ν.prod ν') (OmTyp v Λ g r) =
      μG K1s / a' * ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) := by
    rw [Measure.prod_apply hOmm, ← lintegral_indicator_const hAm]
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    exact hslice x hx
  unfold Mv
  rw [hprod, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
  congr 1
  calc μG K1s / a' * ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * (a * a')
      = (ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * a) * (μG K1s / a' * a') := by ring
    _ = μG K * μG K1s := by rw [hWK, ENNReal.div_mul_cancel ha0'.1 ha0'.2]

end PI.LocMassTypW
