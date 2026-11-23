import Mathlib

open MeasureTheory

namespace GlobalTheory.IwasawaShape

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableInv G] in
theorem lintegral_mul_left_of_map {ρ : Measure G} {p : G} (h : ρ.map (fun g => p * g) = ρ) (f : G → ENNReal)
    (hf : Measurable f) : ∫⁻ x, f (p * x) ∂ρ = ∫⁻ x, f x ∂ρ := by
  have e := lintegral_map (μ := ρ) hf (measurable_const_mul p)
  rw [h] at e
  exact e.symm

theorem exists_map_mul_right_eq_smul (P : Subgroup G) (hP : MeasurableSet (P : Set G)) (ρ : Measure G)
    [SigmaFinite ρ] (h0 : ρ (P : Set G)ᶜ = 0) (hinv : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) (l : G) (hl : l ∈ P) :
    ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * l) = D • ρ := by
  classical
  have e : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hP
  have : MeasurableMul₂ P := ⟨e.measurable_comp_iff.1
    ((measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd))⟩
  have : MeasurableInv P := ⟨e.measurable_comp_iff.1 measurable_subtype_coe.inv⟩
  set ρ' : Measure P := ρ.comap Subtype.val with hρ'
  have hmap : ρ'.map Subtype.val = ρ := by
    rw [hρ', e.map_comap, Subtype.range_coe_subtype, Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 h0
  have inj : ∀ α β : Measure P, α.map Subtype.val = β.map Subtype.val → α = β := fun α β h => by
    rw [← e.comap_map α, ← e.comap_map β, h]
  have : SigmaFinite ρ' :=
    SigmaFinite.of_map ρ' measurable_subtype_coe.aemeasurable (by rw [hmap]; infer_instance)
  have : ρ'.IsMulLeftInvariant := ⟨fun s => inj _ _ (by
    rw [Measure.map_map measurable_subtype_coe (measurable_const_mul s)]
    have hc : (Subtype.val ∘ fun x : P => s * x) = (fun g : G => (s : G) * g) ∘ Subtype.val := rfl
    rw [hc, ← Measure.map_map (measurable_const_mul _) measurable_subtype_coe, hmap, hinv s s.2])⟩
  let l' : P := ⟨l, hl⟩
  set ν' : Measure P := ρ'.map (fun x => x * l') with hν'
  have : ν'.IsMulLeftInvariant := ⟨fun s => by
    rw [hν', Measure.map_map (measurable_const_mul s) (measurable_mul_const l')]
    have hc : ((fun x : P => s * x) ∘ fun x => x * l') = (fun x => x * l') ∘ (fun x => s * x) := by
      funext x; simp [Function.comp, mul_assoc]
    rw [hc, ← Measure.map_map (measurable_mul_const l') (measurable_const_mul s), map_mul_left_eq_self]⟩
  have : SigmaFinite ν' := SigmaFinite.of_map ν' (measurable_mul_const l'⁻¹).aemeasurable (by
    rw [hν', Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
    have hc : ((fun x : P => x * l'⁻¹) ∘ fun x => x * l') = id := by funext x; simp
    rw [hc, Measure.map_id]; infer_instance)
  have hρT' : ρ' (Subtype.val ⁻¹' T) = ρ T := by
    rw [hρ', e.comap_apply, Set.image_preimage_eq_inter_range]
    exact measure_inter_conull (by rw [Subtype.range_coe_subtype]; exact h0)
  have hEq := measure_eq_div_smul ν' ρ' (s := Subtype.val ⁻¹' T) (by rw [hρT']; exact hT0)
    (by rw [hρT']; exact hT1)
  set D := ν' (Subtype.val ⁻¹' T) / ρ' (Subtype.val ⁻¹' T) with hD
  have hmapD : ρ.map (fun g => g * l) = D • ρ := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_map (measurable_mul_const l) measurable_subtype_coe]
    have hc : ((fun g : G => g * l) ∘ Subtype.val) = Subtype.val ∘ (fun x : P => x * l') := rfl
    rw [hc, ← Measure.map_map measurable_subtype_coe (measurable_mul_const l'), ← hν', hEq,
      Measure.map_smul, hmap]
  have huniv : (ρ.map fun g => g * l) Set.univ ≠ 0 := by
    rw [Measure.map_apply (measurable_mul_const l) MeasurableSet.univ, Set.preimage_univ]
    exact fun h => hT0 (measure_mono_null (Set.subset_univ _) h)
  have hD0 : D ≠ 0 := by
    intro h
    apply huniv
    rw [hmapD, h, zero_smul, Measure.coe_zero, Pi.zero_apply]
  have hD1 : D ≠ ⊤ := by
    intro h
    have : SigmaFinite (ρ.map fun g => g * l) :=
      SigmaFinite.of_map _ (measurable_mul_const l⁻¹).aemeasurable (by
        rw [Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
        have hc : ((fun g : G => g * l⁻¹) ∘ fun g => g * l) = id := by funext x; simp
        rw [hc, Measure.map_id]; infer_instance)
    obtain ⟨n, hn⟩ : ∃ n, (ρ.map fun g => g * l) (spanningSets (ρ.map fun g => g * l) n) ≠ 0 := by
      by_contra hne
      push Not at hne
      apply huniv
      rw [← iUnion_spanningSets (ρ.map fun g => g * l)]
      exact measure_iUnion_null hne
    have hlt := measure_spanningSets_lt_top (ρ.map fun g => g * l) n
    set Sn := spanningSets (ρ.map fun g => g * l) n
    rw [hmapD, Measure.smul_apply, smul_eq_mul, h] at hn hlt
    rcases eq_or_ne (ρ Sn) 0 with h' | h'
    · exact hn (by rw [h', mul_zero])
    · rw [ENNReal.top_mul h'] at hlt
      exact lt_irrefl _ hlt
  exact ⟨D, hD0, hD1, hmapD⟩

theorem exists_lintegral_eq_mul (μ ρ κ : Measure G) [SigmaFinite μ] [SFinite ρ] [IsProbabilityMeasure κ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (hμ : μ ≠ 0) (P K : Set G)
    (hKl : ∀ k ∈ K, κ.map (fun g => k * g) = κ) (hPl : ∀ p ∈ P, ρ.map (fun g => p * g) = ρ)
    (hPr : ∀ p ∈ P, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * p) = D • ρ)
    (hdec : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) (T : Set G) (hT : MeasurableSet T)
    (hTK : ∀ k ∈ K, ∀ g, k⁻¹ * g ∈ T ↔ g ∈ T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μ = c * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
  classical
  have hind : Measurable (T.indicator (1 : G → ENNReal)) := measurable_one.indicator hT
  have ind_ne_top : ∀ x, T.indicator (1 : G → ENNReal) x ≠ ⊤ := fun x => by
    by_cases hx : x ∈ T <;> simp [Set.indicator_apply, hx]
  have hLm : ∀ φ : G → ENNReal, Measurable φ →
      Measurable fun h => T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ :=
    fun φ hφ => (hind.comp measurable_inv).mul
      ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.2 * y.1.1 * y.2)).lintegral_prod_right').lintegral_prod_right'

  have key : ∀ h : G, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ = D * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
    intro h
    obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec h
    obtain ⟨D, hD0, hDt, hD⟩ := hPr p0 hp0
    refine ⟨D, hD0, hDt, fun φ hφ => ?_⟩
    have hF : Measurable fun x => ∫⁻ k, φ (x * k) ∂κ := (hφ.comp measurable_mul).lintegral_prod_right'
    have e1 : ∀ q, ∫⁻ k, φ (q * (p0 * k0) * k) ∂κ = ∫⁻ k, φ (q * p0 * k) ∂κ := by
      intro q
      have := lintegral_mul_left_of_map (hKl k0 hk0) (fun k => φ (q * p0 * k))
        (hφ.comp (measurable_const_mul _))
      simpa only [mul_assoc] using this
    simp_rw [e1]
    have := lintegral_map (μ := ρ) hF (measurable_mul_const p0)
    rw [hD, lintegral_smul_measure, smul_eq_mul] at this
    exact this.symm

  have mix : ∀ φ : G → ENNReal, Measurable φ →
      ρ T * ∫⁻ g, φ g ∂μ = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
    intro φ hφ
    have s1 : ∫⁻ g, φ g ∂μ = ∫⁻ g, ∫⁻ k, φ (g * k) ∂κ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g k => φ (g * k)) (by exact (hφ.comp measurable_mul).aemeasurable)]
      simp_rw [lintegral_mul_right_eq_self]
      rw [lintegral_const, measure_univ, mul_one]
    have s2 : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) ∂ρ = ρ T := by
      intro g
      obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec g
      have e : ∀ q, T.indicator (1 : G → ENNReal) ((p0 * k0)⁻¹ * q) = T.indicator 1 (p0⁻¹ * q) := by
        intro q
        have hm : (p0 * k0)⁻¹ * q ∈ T ↔ p0⁻¹ * q ∈ T := by
          rw [mul_inv_rev, mul_assoc]; exact hTK k0 hk0 _
        simp only [Set.indicator_apply, hm, Pi.one_apply]
      simp_rw [e]
      have := lintegral_mul_left_of_map (hPl p0 hp0) (fun x => T.indicator (1 : G → ENNReal) (p0⁻¹ * x))
        (hind.comp (measurable_const_mul _))
      simp only [inv_mul_cancel_left] at this
      rw [← this, lintegral_indicator_one hT]
    have hW1 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ρ T * ∫⁻ g, φ g ∂μ := by
      have e : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ
          = ρ T * ∫⁻ k, φ (g * k) ∂κ := by
        intro g
        exact (lintegral_mul_const _ (hind.comp (measurable_const_mul g⁻¹))).trans (congrArg (· * _) (s2 g))
      simp_rw [e]
      rw [lintegral_const_mul' _ _ hT1, ← s1]
    have hmF : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) (x.1⁻¹ * x.2) * ∫⁻ k, φ (x.1 * k) ∂κ :=
      (hind.comp (measurable_fst.inv.mul measurable_snd)).mul
        (((hφ.comp measurable_mul).lintegral_prod_right').comp measurable_fst)
    have hmG : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) x.2⁻¹ * ∫⁻ k, φ (x.1 * x.2 * k) ∂κ :=
      (hind.comp measurable_snd.inv).mul
        ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.1 * y.1.2 * y.2)).lintegral_prod_right')
    have hW2 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g q => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
        ∫⁻ k, φ (g * k) ∂κ) (by exact hmF.aemeasurable)]
      have e : ∀ q, ∫⁻ g, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂μ
          = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ k, φ (q * h * k) ∂κ ∂μ := by
        intro q
        refine (lintegral_mul_left_eq_self (μ := μ) (fun g => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
          ∫⁻ k, φ (g * k) ∂κ) q).symm.trans ?_
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      simp_rw [e]
      rw [lintegral_lintegral_swap (f := fun q h => T.indicator (1 : G → ENNReal) h⁻¹ *
        ∫⁻ k, φ (q * h * k) ∂κ) (by exact hmG.aemeasurable)]
      exact lintegral_congr fun h => lintegral_const_mul' _ _ (ind_ne_top _)
    rw [← hW1, hW2]

  obtain ⟨S, hS, hS0, hS1⟩ : ∃ S, MeasurableSet S ∧ μ S ≠ 0 ∧ μ S ≠ ⊤ := by
    by_contra hne
    push Not at hne
    apply hμ
    have hz : ∀ n, μ (spanningSets μ n) = 0 := fun n => by
      by_contra hn
      exact (measure_spanningSets_lt_top μ n).ne (hne _ (measurableSet_spanningSets μ n) hn)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
    exact measure_iUnion_null hz
  have hφ0 : Measurable (S.indicator (1 : G → ENNReal)) := measurable_one.indicator hS
  have hμS : ∫⁻ g, S.indicator (1 : G → ENNReal) g ∂μ = μ S := lintegral_indicator_one hS
  have mix0 := mix _ hφ0
  rw [hμS] at mix0
  have hL0 : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ 0 := by
    intro h0
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ = 0 := by
      refine (lintegral_congr fun h => ?_).trans lintegral_zero
      obtain ⟨D, -, -, hD⟩ := key h
      rw [hD _ hφ0, h0, mul_zero, mul_zero]
    rw [this] at mix0
    exact mul_ne_zero hT0 hS0 mix0
  have hLt : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ ⊤ := by
    intro ht
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ
        = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤ := by
      rw [← (lintegral_mul_const ⊤ (hind.comp measurable_inv) : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ⊤ ∂μ = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤)]
      refine lintegral_congr fun h => ?_
      obtain ⟨D, hD0, -, hD⟩ := key h
      rw [hD _ hφ0, ht, ENNReal.mul_top hD0]
    rw [this] at mix0
    rcases eq_or_ne (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) 0 with hz | hz
    · rw [hz, zero_mul] at mix0
      exact mul_ne_zero hT0 hS0 mix0
    · rw [ENNReal.mul_top hz] at mix0
      exact ENNReal.mul_ne_top hT1 hS1 mix0
  refine ⟨μ S / ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ,
    (ENNReal.div_pos_iff.2 ⟨hS0, hLt⟩).ne', ENNReal.div_ne_top hS1 hL0, fun φ hφ => ?_⟩
  have E : ρ T * ((∫⁻ g, φ g ∂μ) * ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ)
      = ρ T * (μ S * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ) := by
    rw [← mul_assoc]
    rw [mix _ hφ]
    rw [← lintegral_mul_const _ (hLm _ hφ)]
    rw [← mul_assoc]
    rw [mix0]
    rw [← lintegral_mul_const _ (hLm _ hφ0)]
    refine lintegral_congr fun h => ?_
    obtain ⟨D, -, -, hD⟩ := key h
    rw [hD _ hφ, hD _ hφ0]
    ring
  have E' := (ENNReal.mul_right_inj hT0 hT1).1 E
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  exact (ENNReal.eq_div_iff hL0 hLt).2 (by rw [mul_comm]; exact E')

end GlobalTheory.IwasawaShape
