import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockPSDCongr

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section L2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gramL {ι : Type} (μ : Measure ℂ) (F G : ι × ℂ → ℂ → H) (p q : ι × ℂ) : ℂ :=
  ∫ D, ⟪F p D, G q D⟫_ℂ ∂μ

theorem inner_toLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ D, ⟪f D, g D⟫_ℂ ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun D => ⟪f D, g D⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem blockPSD_gramL {ι : Type} (μ : Measure ℂ) (Y : Finset ι) (U A : ι × ℂ → ℂ → H)
    (memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (U (h, x)) 2 μ)
    (memA : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (A (h, x)) 2 μ) (Xs : Finset ℂ) (hXs : ∀ x ∈ Xs, x ≠ 0) :
    KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL μ U U) (gramL μ U A) (gramL μ A A) := by
  have hmem : ∀ p ∈ Y ×ˢ Xs, MemLp (U p) 2 μ ∧ MemLp (A p) 2 μ := by
    intro p hp
    rw [Finset.mem_product] at hp
    have hx := hXs _ hp.2
    exact ⟨memU _ hp.1 _ hx, memA _ hp.1 _ hx⟩
  let v : {x // x ∈ (Y ×ˢ Xs).disjSum (Y ×ˢ Xs)} → Lp H 2 μ := fun x =>
    Sum.elim (fun p => if hp : MemLp (U p) 2 μ then hp.toLp (U p) else 0)
      (fun q => if hq : MemLp (A q) 2 μ then hq.toLp (A q) else 0) x.1
  unfold KB.BlockPSD TB.PSDOn
  open scoped ComplexOrder in
  refine (congrArg Matrix.PosSemidef ?_).mpr (Matrix.posSemidef_gram ℂ v)
  ext i j
  obtain ⟨x, hx⟩ := i
  obtain ⟨y, hy⟩ := j
  rcases x with p | q <;> rcases y with p' | q'
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2,
      inner_toLp h1 h2, gramL]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2, gramL]
    rw [← inner_conj_symm, inner_toLp h2 h1]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inr, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]

theorem exists_compact_tail (μ : Measure ℂ) [NullSingletonClass μ] (φ : ℂ → ℝ) (hφ : Integrable φ μ) (η : ℝ) (hη : 0 < η) :
    ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧ ∫ D in Kᶜ, φ D ∂μ < η := by
  let K : ℕ → Set ℂ := fun n => {D | ((n : ℝ) + 1)⁻¹ ≤ ‖D‖ ∧ ‖D‖ ≤ (n : ℝ) + 1}
  have hKc : ∀ n, IsCompact (K n) := fun n => by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (n : ℝ) + 1)).subset fun D hD => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hD.2
  have hK0 : ∀ n, (0 : ℂ) ∉ K n := fun n h => by
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.mpr (by positivity))
  have hmono : Monotone K := by
    intro m n hmn D hD
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
    exact ⟨le_trans (inv_anti₀ (by positivity) h) hD.1, hD.2.trans h⟩
  have hKm : ∀ n, MeasurableSet (K n)ᶜ := fun n => (hKc n).isClosed.measurableSet.compl
  have hanti : Antitone fun n => (K n)ᶜ := fun m n h => Set.compl_subset_compl.mpr (hmono h)
  have hinter : ⋂ n, (K n)ᶜ = {0} := by
    ext D
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hD
      obtain ⟨n, hn⟩ := exists_nat_ge (max ‖D‖ ‖D‖⁻¹)
      have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
      apply h n
      refine ⟨?_, ?_⟩
      · have h1 : ‖D‖⁻¹ ≤ (n : ℝ) + 1 :=
          (le_max_right _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
        exact inv_le_of_inv_le₀ hpos h1
      · exact (le_max_left _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
    · rintro rfl n
      exact hK0 n
  have ht := tendsto_setIntegral_of_antitone hKm hanti ⟨0, hφ.integrableOn⟩
  have h0 : ∫ x in ({0} : Set ℂ), φ x ∂μ = 0 := by
    rw [Measure.restrict_eq_zero.mpr (measure_singleton 0), integral_zero_measure]
  rw [hinter, h0] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hη)).exists
  exact ⟨K n, hKc n, hK0 n, hn⟩

theorem tendsto_integral_inner_germ {α : Type} {l : Filter α} (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    [NullSingletonClass μ] (F G : α → ℂ → H) (g : ℂ → ℝ) (hg : MemLp g 2 μ) (B : ℝ)
    (hF : ∀ᶠ x in l, MemLp (F x) 2 μ ∧ ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B)
    (hG : ∀ᶠ x in l, ∀ᵐ D ∂μ, ‖G x D‖ ≤ g D)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in l, ∀ᵐ D ∂μ, D ∈ K → ‖F x D‖ ≤ δ) :
    Tendsto (fun x => ∫ D, ⟪F x D, G x D⟫_ℂ ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hB1p : 0 < max B 0 + 1 := by positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = ε / (4 * (max B 0 + 1)) := ⟨_, rfl⟩
  have hlamp : 0 < lam := by rw [hlam]; positivity
  have hg2 : Integrable (fun D => g D ^ 2) μ := (memLp_two_iff_integrable_sq hg.1).1 hg
  obtain ⟨K, hK, h0K, hKt⟩ := exists_compact_tail μ _ hg2 (lam * ε / 2) (by positivity)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hgK : IntegrableOn (fun D => |g D|) K μ := ((hg.restrict K).integrable one_le_two).abs
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ D in K, |g D| ∂μ := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hI]; exact setIntegral_nonneg hKm fun D _ => abs_nonneg _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (4 * (I + 1)) := ⟨_, rfl⟩
  have hδp : 0 < δ := by rw [hδ]; positivity
  filter_upwards [hF, hG, hloc K hK h0K δ hδp] with x hFx hGb hFK
  obtain ⟨hFm, hFB⟩ := hFx
  rw [dist_zero_right]
  have hF2 : Integrable (fun D => ‖F x D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hFm.1).1 hFm
  have i1 : Integrable (fun D => δ * K.indicator (fun D => |g D|) D) μ :=
    (hgK.integrable_indicator hKm).const_mul δ
  have i2 : Integrable (fun D => lam * ‖F x D‖ ^ 2) μ := hF2.const_mul lam
  have i3 : Integrable (fun D => Kᶜ.indicator (fun D => g D ^ 2) D / lam) μ :=
    (hg2.indicator hKm.compl).div_const lam
  have i4 : Integrable (fun D => (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) μ :=
    (i2.add i3).div_const 2
  have hpt : ∀ᵐ D ∂μ, ‖⟪F x D, G x D⟫_ℂ‖ ≤ δ * K.indicator (fun D => |g D|) D +
      (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2 := by
    filter_upwards [hGb, hFK] with D hb hk
    have h1 : ‖⟪F x D, G x D⟫_ℂ‖ ≤ ‖F x D‖ * g D :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    have hg0 : 0 ≤ g D := (norm_nonneg _).trans hb
    by_cases hDK : D ∈ K
    · have hFD := hk hDK
      rw [Set.indicator_of_mem hDK, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hDK), abs_of_nonneg hg0]
      have : ‖F x D‖ * g D ≤ δ * g D := mul_le_mul_of_nonneg_right hFD hg0
      have : 0 ≤ lam * ‖F x D‖ ^ 2 := by positivity
      have : (lam * ‖F x D‖ ^ 2 + 0 / lam) / 2 ≥ 0 := by rw [zero_div, add_zero]; positivity
      linarith
    · rw [Set.indicator_of_notMem hDK, Set.indicator_of_mem (Set.mem_compl hDK)]
      have key : lam * ‖F x D‖ ^ 2 + g D ^ 2 / lam - 2 * (‖F x D‖ * g D) = (lam * ‖F x D‖ - g D) ^ 2 / lam := by
        field_simp
        ring
      have : 0 ≤ (lam * ‖F x D‖ - g D) ^ 2 / lam := by positivity
      have : δ * 0 = 0 := mul_zero δ
      linarith
  have hInt : ∫ D, (δ * K.indicator (fun D => |g D|) D +
      (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) ∂μ =
      δ * I + (lam * ∫ D, ‖F x D‖ ^ 2 ∂μ + (∫ D in Kᶜ, g D ^ 2 ∂μ) / lam) / 2 := by
    rw [integral_add i1 i4, integral_const_mul, integral_indicator hKm, integral_div, integral_add i2 i3,
      integral_const_mul, integral_div, integral_indicator hKm.compl, hI]
  have e1 : δ * I ≤ ε / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have e2 : lam * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ ε / 4 := by
    have hle : ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ max B 0 + 1 := by linarith [le_max_left B 0]
    calc lam * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ lam * (max B 0 + 1) := mul_le_mul_of_nonneg_left hle hlamp.le
      _ = ε / 4 := by rw [hlam]; field_simp
  have e3 : (∫ D in Kᶜ, g D ^ 2 ∂μ) / lam < ε / 2 := by
    rw [div_lt_iff₀ hlamp]
    linarith
  calc ‖∫ D, ⟪F x D, G x D⟫_ℂ ∂μ‖ ≤ ∫ D, ‖⟪F x D, G x D⟫_ℂ‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ D, (δ * K.indicator (fun D => |g D|) D +
        (lam * ‖F x D‖ ^ 2 + Kᶜ.indicator (fun D => g D ^ 2) D / lam) / 2) ∂μ :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (i1.add i4) hpt
    _ = _ := hInt
    _ < ε := by linarith

end L2

end

end Formalism.FourierDecayAlt.P.PBK
