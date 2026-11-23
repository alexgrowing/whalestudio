import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix Topology

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.Average

theorem integral_comp_finite {G V : Type*} [MeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ] (F : G → V)
    (T : Finset V) (hT : ∀ᵐ g ∂μ, F g ∈ T) (hm : ∀ v, MeasurableSet (F ⁻¹' {v})) (φ : V → ℂ) :
    ∫ g, φ (F g) ∂μ = ∑ v ∈ T, (μ.real (F ⁻¹' {v}) : ℂ) * φ v := by
  classical
  have h1 : (fun g => φ (F g)) =ᵐ[μ] fun g => ∑ v ∈ T, (F ⁻¹' {v}).indicator (fun _ => φ v) g := by
    filter_upwards [hT] with g hg
    rw [Finset.sum_eq_single (F g)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro v _ hv
      exact Set.indicator_of_notMem (by simpa using hv.symm) _
    · exact fun h => absurd hg h
  rw [integral_congr_ae h1, integral_finset_sum _ fun v _ => (integrable_const _).indicator (hm v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hm v), Complex.real_smul]

theorem sb_left_invariant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) :
    ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X : Matrix (Fin n) (Fin d) k, Ψ (u.val * X) = Ψ X := by
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X ∈ tsupport Ψ, Ψ (u.val * X) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin n) k × Matrix (Fin n) (Fin d) k => (Ψ (q.1.val * q.2), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.one_mul] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X ∈ tsupport Ψ, Ψ ((u⁻¹).val * X) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin n) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin n) k))
    exact ht.eventually h1
  filter_upwards [h1, h3] with u hu1 hu2 X
  by_cases hX : X ∈ tsupport Ψ
  · exact hu1 X hX
  by_cases hX' : u.val * X ∈ tsupport Ψ
  · have := hu2 _ hX'
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem mem_augRk_of_smallF_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ (S : Set (Matrix (Fin n) (Fin d) k)),
    (∀ (E : GL (Fin n) k), ∀ Y ∈ S, E.val * Y ∈ S → E ∈ GlobalTheory.SplitWeil.KO k (Fin n)) →
    (∀ E ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y ∈ S, E.val * Y ∈ S) →
    ∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) →
    (∀ Y ∈ S, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = 0) → Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hν S hrig hst Φ hΦ hsupp h0
  have : BorelSpace (GL (Fin n) k) := borel_GL
  set K := GlobalTheory.SplitWeil.KO k (Fin n) with hK
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := isOpen_KO
  have hKm : MeasurableSet (K : Set (GL (Fin n) k)) := hKo.measurableSet
  have hK1 : haarVol K K = 1 := haarVol_self isOpen_KO le_rfl
  let F : GL (Fin n) k → Matrix (Fin n) (Fin d) k → ℂ :=
    fun g Y => Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)
  have hFl : ∀ g, F g = lact ν (invT g)⁻¹ Φ := fun g => by
    funext Y
    have e1 : gdet (invT g)⁻¹ = gdet g := by
      rw [show gdet (invT g)⁻¹ = (gdet (invT g))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
    simp only [F, lact, e1, invT_inv_val, Matrix.transpose_transpose, Fintype.card_fin]
    ring
  have hev : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ g, F (u * g) = F g := by
    have h2 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ν (gdet u) = 1 := by
      have : IsOpen ((fun u : GL (Fin n) k => Matrix.GeneralLinearGroup.det u) ⁻¹' (ν.ker : Set kˣ)) :=
        IsOpen.preimage Matrix.GeneralLinearGroup.continuous_det hν
      exact this.mem_nhds (by simp)
    filter_upwards [sb_left_invariant Φ hΦ.1, h2, hKo.mem_nhds (one_mem K)] with u h1 h2 h3 g
    funext Y
    simp only [F, gdet_mul, map_mul, h2, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO h3),
      Units.val_mul, Matrix.mul_assoc, h1, one_mul]
  have hlc : IsLocallyConstant F := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have ht : Filter.Tendsto (fun y : GL (Fin n) k => y * x⁻¹) (𝓝 x) (𝓝 1) := by
      simpa using ((continuous_mul_const x⁻¹).tendsto x)
    filter_upwards [ht.eventually hev] with y hy
    simpa using hy x
  have hfin : (F '' K).Finite := by
    have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_KO (k := k) (n := Fin n))
    have h := (hlc.comp_continuous (continuous_subtype_val (p := fun g => g ∈ K))).range_finite
    refine h.subset ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  set μ := (haarVol K).restrict K with hμ
  have hμ1 : μ Set.univ = 1 := by rw [hμ, Measure.restrict_apply_univ, hK1]
  have : IsFiniteMeasure μ := ⟨by rw [hμ1]; exact ENNReal.one_lt_top⟩
  have hI := integral_comp_finite μ F hfin.toFinset
    (by
      filter_upwards [ae_restrict_mem hKm] with g hg
      exact hfin.mem_toFinset.2 ⟨g, hg, rfl⟩)
    (fun v => (hlc.isOpen_fiber v).measurableSet)
  have hs1 : ∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) = 1 := by
    have := hI fun _ => 1
    simpa [Measure.real, hμ1] using this.symm
  have hA : ∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) • v = 0 := by
    funext Y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hI fun v => v Y]
    by_cases hY : Y ∈ S
    · rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact h0 Y hY
      · intro g hg
        have : g.val * Y ∉ S := fun h => hg (hrig g Y hY h)
        simp [F, hsupp _ this]
    · refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
      have : g.val * Y ∉ S := fun h => hY (by
        have := hst g⁻¹ (inv_mem hg) _ h
        rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this)
      simp [F, hsupp _ this]
  have hΦe : Φ = -∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) • (v - Φ) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hA, ← Finset.sum_smul, hs1, one_smul, zero_sub, neg_neg]
  rw [hΦe]
  refine neg_mem (Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ ?_)
  obtain ⟨g, -, rfl⟩ := hfin.mem_toFinset.1 hv
  exact Submodule.subset_span ⟨(invT g)⁻¹, Φ, hΦ, by rw [hFl]⟩

end GlobalTheory.FullRankCoinv.Average
