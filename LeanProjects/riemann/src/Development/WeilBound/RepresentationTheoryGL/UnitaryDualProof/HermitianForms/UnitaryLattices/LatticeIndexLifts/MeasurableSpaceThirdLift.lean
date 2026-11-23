import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.MeasurableSpaceSecondLift

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Main

local instance measurableSpaceThirdLift : MeasurableSpace k := borel k
local instance borelSpaceThirdLift : BorelSpace k := ⟨rfl⟩
local instance instSCK3 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in

theorem cov {K : Set (Fin (m + 1) → k)} (hK : IsCompact K) (h0 : (0 : Fin (m + 1) → k) ∉ K) (v : V) :
    ∫⁻ ξ in K, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B v v).re := by
  classical
  have hloc : ∀ ζ ∈ K, ∃ M₀ : AddSubgroup (Fin (m + 1) → k), Lat M₀ ∧
      ∀ ξ, ξ - ζ ∈ perp ψ M₀ → Df gl s C ξ v v = Df gl s C ζ v v ∧
        ∀ M : AddSubgroup (Fin (m + 1) → k), Lat M → M₀ ≤ M →
          (Df gl s C ζ v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col ξ M v) v).re :=
    fun ζ hζ => locB hψ hψ1 hS hA₀ hBg hD hCp hC hCB hν (fun h => h0 (h ▸ hζ)) v
  choose! M₀ hM₀L hM₀ using hloc
  obtain ⟨F, hFK, hFfin, hFcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun ζ => (fun ξ => ξ - ζ) ⁻¹' (perp ψ (M₀ ζ) : Set (Fin (m + 1) → k)))
    (fun ζ hζ => (perp_open ψ hψ hψ1 (hM₀L ζ hζ)).preimage (continuous_sub_right ζ))
    (fun ζ hζ => Set.mem_biUnion hζ (by simp))
  have hcomp : IsCompact (⋃ ζ ∈ F, (M₀ ζ : Set (Fin (m + 1) → k))) :=
    hFfin.isCompact_biUnion fun ζ hζ => (hM₀L ζ (hFK hζ)).1
  obtain ⟨M, hML, hMsub⟩ := lat_over hcomp
  have hMle : ∀ ζ ∈ F, M₀ ζ ≤ M := fun ζ hζ x hx => hMsub (Set.mem_biUnion hζ hx)
  have hPle : ∀ ζ ∈ F, perp ψ M ≤ perp ψ (M₀ ζ) := fun ζ hζ => perp_anti ψ (hMle ζ hζ)
  have hPo : IsOpen (perp ψ M : Set (Fin (m + 1) → k)) := perp_open ψ hψ hψ1 hML
  obtain ⟨T, hTK, hTfin, hTcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun t => (fun ξ => ξ - t) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)))
    (fun t _ => hPo.preimage (continuous_sub_right t))
    (fun ξ hξ => Set.mem_biUnion hξ (by simp))
  let q : (Fin (m + 1) → k) → (Fin (m + 1) → k) ⧸ perp ψ M := QuotientAddGroup.mk
  have hq : ∀ a b, q a = q b → a - b ∈ perp ψ M := fun a b h => by
    have h1 := (perp ψ M).neg_mem (QuotientAddGroup.eq.mp h)
    rwa [show -(-a + b) = a - b by abel] at h1
  have hq' : ∀ a b, a - b ∈ perp ψ M → q a = q b := fun a b h => by
    apply QuotientAddGroup.eq.mpr
    rw [show -a + b = -(a - b) by abel]
    exact (perp ψ M).neg_mem h
  have hout : ∀ t, q (q t).out = q t := fun t => QuotientAddGroup.out_eq' (q t)
  let S : Finset (Fin (m + 1) → k) := hTfin.toFinset.image (fun t => (q t).out)
  have hSF : ∀ η ∈ S, ∃ ζ ∈ F, ∀ ξ, ξ - η ∈ perp ψ M → ξ - ζ ∈ perp ψ (M₀ ζ) := by
    intro η hη
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hη
    have htK : t ∈ K := hTK (hTfin.mem_toFinset.mp ht)
    obtain ⟨ζ, hζ, hζt⟩ := Set.mem_iUnion₂.mp (hFcov htK)
    refine ⟨ζ, hζ, fun ξ hξ => ?_⟩
    have h1 : (q t).out - t ∈ perp ψ M := hq _ _ (hout t)
    have h2 : ξ - ζ = (ξ - (q t).out) + ((q t).out - t) + (t - ζ) := by abel
    rw [h2]
    exact add_mem (add_mem (hPle ζ hζ hξ) (hPle ζ hζ h1)) (show t - ζ ∈ perp ψ (M₀ ζ) from hζt)
  have hSd : ∀ η ∈ S, ∀ η' ∈ S, η - η' ∈ perp ψ M → η = η' := by
    intro η hη η' hη' h
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hη
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.mp hη'
    have h1 := hq' _ _ h
    rw [hout, hout] at h1
    rw [h1]
  have hKS : K ⊆ ⋃ η ∈ S, (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)) := by
    intro ξ hξ
    obtain ⟨t, ht, hξt⟩ := Set.mem_iUnion₂.mp (hTcov hξ)
    refine Set.mem_iUnion₂.mpr ⟨(q t).out, Finset.mem_image.mpr ⟨t, hTfin.mem_toFinset.mpr ht, rfl⟩, ?_⟩
    have h1 : t - (q t).out ∈ perp ψ M := hq _ _ (hout t).symm
    show ξ - (q t).out ∈ perp ψ M
    rw [show ξ - (q t).out = (ξ - t) + (t - (q t).out) by abel]
    exact add_mem (show ξ - t ∈ perp ψ M from hξt) h1
  have hdisj : Set.PairwiseDisjoint (↑S)
      (fun η => (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k))) := by
    intro η hη η' hη' hne
    refine Set.disjoint_left.mpr fun ξ h1 h2 => hne (hSd η hη η' hη' ?_)
    rw [show η - η' = (ξ - η') - (ξ - η) by abel]
    exact sub_mem (show ξ - η' ∈ perp ψ M from h2) (show ξ - η ∈ perp ψ M from h1)
  have hPfin : ν (perp ψ M) < ∞ := meas_perp_lt_top ψ ν hψ hψ1 hML
  have hbd : ∀ η ∈ S, (Df gl s C η v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col η M v) v).re ∧
      ∃ ζ ∈ F, Df gl s C η v v = Df gl s C ζ v v ∧
        ∀ ξ, ξ - η ∈ perp ψ M → Df gl s C ξ v v = Df gl s C η v v := by
    intro η hη
    obtain ⟨ζ, hζ, hζη⟩ := hSF η hη
    have hζK := hFK hζ
    have e0 : Df gl s C η v v = Df gl s C ζ v v := ((hM₀ ζ hζK) η (hζη η (by simp))).1
    have hb := ((hM₀ ζ hζK) η (hζη η (by simp))).2 M hML (hMle ζ hζ)
    refine ⟨by rw [e0]; exact hb, ζ, hζ, e0, fun ξ hξ => ?_⟩
    rw [e0]
    exact ((hM₀ ζ hζK) ξ (hζη ξ hξ)).1
  have step : ∀ η ∈ S, ∫⁻ ξ in (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
      ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B (av ψ col η M v) v).re := by
    intro η hη
    obtain ⟨hb, -, -, -, hc⟩ := hbd η hη
    rw [setLIntegral_congr_fun (g := fun _ => ENNReal.ofReal (Df gl s C η v v).re)
      (hPo.preimage (continuous_sub_right η)).measurableSet
      (fun ξ hξ => by simp only; rw [hc ξ hξ]), setLIntegral_const]
    have hmeas : ν ((fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k))) = ν (perp ψ M) := by
      simp only [sub_eq_add_neg]
      exact measure_preimage_add_right ν (-η) _
    rw [hmeas, ← ENNReal.ofReal_toReal hPfin.ne, ← ENNReal.ofReal_mul (Df_re_nonneg hCp η v)]
    exact ENNReal.ofReal_le_ofReal hb
  have hnn : ∀ η ∈ S, 0 ≤ (B (av ψ col η M v) v).re := fun η hη =>
    le_trans (mul_nonneg (Df_re_nonneg hCp η v) ENNReal.toReal_nonneg) (hbd η hη).1
  have hbes := av_bessel ψ hψ col hS.col_zero hS.col_add hS.smooth_col B hBp hBc M hML S hSd v
  calc ∫⁻ ξ in K, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν
      ≤ ∫⁻ ξ in ⋃ η ∈ S, (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
          ENNReal.ofReal (Df gl s C ξ v v).re ∂ν := lintegral_mono_set hKS
    _ = ∑ η ∈ S, ∫⁻ ξ in (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
          ENNReal.ofReal (Df gl s C ξ v v).re ∂ν :=
        lintegral_biUnion_finset hdisj (fun η _ => (hPo.preimage (continuous_sub_right η)).measurableSet) _
    _ ≤ ∑ η ∈ S, ENNReal.ofReal (B (av ψ col η M v) v).re := Finset.sum_le_sum step
    _ = ENNReal.ofReal (∑ η ∈ S, (B (av ψ col η M v) v).re) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
    _ ≤ ENNReal.ofReal (B v v).re := ENNReal.ofReal_le_ofReal hbes

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in

theorem bessel (v : V) : ∫⁻ ξ, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B v v).re := by
  classical
  let f : (Fin (m + 1) → k) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Df gl s C ξ v v).re
  have hDm : Measurable fun ξ => Df gl s C ξ v v := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro ζ hζ
    exact (continuousAt_const.congr
      ((Df_loc hS hC hζ v v).mono fun ξ hξ => hξ.symm)).continuousWithinAt
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp hDm)
  obtain ⟨W, hWp, hW⟩ := (nhds_basis_opens (0 : Fin (m + 1) → k)).exists_antitone_subbasis
  let E := CompactExhaustion.choice (Fin (m + 1) → k)
  let K : ℕ → Set (Fin (m + 1) → k) := fun n => E n \ W n
  have hKc : ∀ n, IsCompact (K n) := fun n => (E.isCompact n).diff (hWp n).2
  have h0K : ∀ n, (0 : Fin (m + 1) → k) ∉ K n := fun n h => h.2 (hWp n).1
  have hKmono : Monotone K := fun a b hab => Set.diff_subset_diff (E.subset hab) (hW.antitone hab)
  let g : ℕ → (Fin (m + 1) → k) → ℝ≥0∞ := fun n => (K n).indicator f
  have hgm : ∀ n, Measurable (g n) := fun n => hfm.indicator (hKc n).measurableSet
  have hgmono : Monotone g := fun a b hab ξ =>
    Set.indicator_le_indicator_of_subset (hKmono hab) (fun _ => bot_le) ξ
  have hsup : ∀ ξ, f ξ = ⨆ n, g n ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have hf0 : f 0 = 0 := by simp [f, Df_zero]
      rw [hf0]
      symm
      exact ENNReal.iSup_eq_zero.mpr fun n => by simp [g, Set.indicator_apply, h0K n]
    · obtain ⟨n₁, hn₁⟩ := E.exists_mem ξ
      obtain ⟨i, -, hi⟩ := hW.toHasBasis.mem_iff.mp (isOpen_compl_singleton.mem_nhds (Ne.symm hξ))
      have hmem : ξ ∈ K (max n₁ i) := by
        refine ⟨E.subset (le_max_left _ _) hn₁, fun h => ?_⟩
        exact hi (hW.antitone (le_max_right _ _) h) rfl
      refine le_antisymm (le_iSup_of_le (max n₁ i) ?_) (iSup_le fun n => Set.indicator_le_self _ _ ξ)
      simp [g, Set.indicator_apply, hmem]
  show ∫⁻ ξ, f ξ ∂ν ≤ _
  calc ∫⁻ ξ, f ξ ∂ν = ∫⁻ ξ, ⨆ n, g n ξ ∂ν := lintegral_congr hsup
    _ = ⨆ n, ∫⁻ ξ, g n ξ ∂ν := lintegral_iSup hgm hgmono
    _ ≤ ENNReal.ofReal (B v v).re := iSup_le fun n => by
        simp only [g]
        rw [lintegral_indicator (hKc n).measurableSet]
        exact cov hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν (hKc n) (h0K n) v

omit hψ hψ1 hA₀ hBp hBc hBg hD hCp hCB hν [ν.IsAddHaarMeasure] in
include hS hC in
theorem Df_meas (v w : V) : Measurable fun ξ => Df gl s C ξ v w := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro ζ hζ
  exact (continuousAt_const.congr
    ((Df_loc hS hC hζ v w).mono fun ξ hξ => hξ.symm)).continuousWithinAt

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem integrable_re (v : V) : Integrable (fun ξ => (Df gl s C ξ v v).re) ν := by
  refine ⟨(Complex.measurable_re.comp (Df_meas hS hC v v)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => Df_re_nonneg hCp ξ v)]
  exact lt_of_le_of_lt (bessel hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν v) ENNReal.ofReal_lt_top

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem integrable_Df (v w : V) : Integrable (fun ξ => Df gl s C ξ v w) ν := by
  refine Integrable.mono'
    (((integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν v).add
      (integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν w)).div_const 2)
    (Df_meas hS hC v w).aestronglyMeasurable
    (Eventually.of_forall fun ξ => psd_norm_le _ ⟨Df_herm hCp ξ, Df_re_nonneg hCp ξ⟩ v w)

end Main

end PositivityTheory.RgUd.Form.U.Lift2
