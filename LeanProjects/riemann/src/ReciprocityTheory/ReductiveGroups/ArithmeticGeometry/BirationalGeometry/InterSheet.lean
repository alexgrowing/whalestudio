import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem analyticAt_coord {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : AnalyticAt ℂ γ y) (p : Σ k, ι k) : AnalyticAt ℂ (fun y' => γ y' p) y :=
  analyticAt_pi_iff.mp h p

theorem pot_contDiffAt {L : HermLine ι} (hL : IsSmoothHerm L) {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y := by
  have hh : ContDiffAt ℝ 2 L.h (γ y) :=
    (hL.contDiffAt (isOpen_blockNonzero.mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγr : ContDiffAt ℝ 2 γ y := (hγ.contDiffAt (n := 2)).restrict_scalars ℝ
  exact (hh.comp y hγr).log (L.pos _ hy).ne'

theorem density_eq {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {A : HermLine ι}
    {s : MRing ι} {P : Ideal (MRing ι)} (hs : IsSectionOn P A s)
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    logNorm A s (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
      logNorm A s (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y := by
  obtain ⟨a, ha, hsm, -⟩ := hs
  have hy0 := hy
  choose i0 hi0 using hy0
  obtain ⟨c, hc⟩ : ∃ c : (Fin e → ℂ) → K → ℂ,
      ∀ y' k, c y' k = γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ := ⟨_, fun _ _ => rfl⟩
  have hnz : ∀ᶠ y' in 𝓝 y, ∀ k, γ y' ⟨k, i0 k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (analyticAt_coord hγ ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  have hrel : ∀ᶠ y' in 𝓝 y, (∀ k, γ y' ⟨k, i0 k⟩ ≠ 0) ∧ (∀ k, c y' k ≠ 0) ∧
      γ' y' = bsmul (c y') (γ y') := by
    filter_upwards [hnz, hseg] with y' h0 hs'
    obtain ⟨h1, h2⟩ := eq_bsmul_of_segre_eq i0 h0 hs'
    have hcy : c y' = fun k => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ := funext (hc y')
    refine ⟨h0, fun k => ?_, by rw [hcy]; exact h2⟩
    rw [hc]
    exact div_ne_zero (h1 k) (h0 k)
  obtain ⟨-, hc0, hyrel⟩ := hrel.self_of_nhds
  have hlog : logNorm A s (γ' y) = logNorm A s (γ y) := by
    rw [hyrel]
    exact logNorm_bsmul A ha hsm hc0 _
  rw [hlog]
  congr 1
  have hj : ∀ j, cxHessian (fun y' => pot L j (γ' y')) y = cxHessian (fun y' => pot L j (γ y')) y := by
    intro j
    have hcan : ∀ k, AnalyticAt ℂ (fun y' => c y' k) y := by
      intro k
      have hfun : (fun y' => c y' k) = fun y' => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ :=
        funext fun y' => hc y' k
      rw [hfun]
      exact (analyticAt_coord hγ' _).div (analyticAt_coord hγ _) (hi0 k)
    have hG : AnalyticAt ℂ
        (fun y' => ∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)) y := by
      have hk : ∀ k, AnalyticAt ℂ
          (fun y' => (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)) y := by
        intro k
        refine analyticAt_const.mul (((hcan k).div analyticAt_const (hc0 k)).clog ?_)
        show c y k / c y k ∈ Complex.slitPlane
        rw [div_self (hc0 k)]
        exact Complex.one_mem_slitPlane
      have h := Finset.analyticAt_sum (𝕜 := ℂ)
        (f := fun (k : K) (y' : Fin e → ℂ) => (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k))
        (c := y) Finset.univ (fun k _ => hk k)
      convert h using 1
      funext y'
      rw [Finset.sum_apply]
    have hev : (fun y' => pot L j (γ' y')) =ᶠ[𝓝 y] fun y' => pot L j (γ y') +
        (∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)).re +
        ∑ k, ((L j).a k : ℝ) * Real.log ‖c y k‖ := by
      filter_upwards [hrel] with y' hy'
      obtain ⟨h0, hck, h2⟩ := hy'
      have hpos : 0 < (L j).h (γ y') := (L j).pos _ fun k => ⟨i0 k, h0 k⟩
      have hne : ∀ k ∈ Finset.univ, ‖c y' k‖ ^ (L j).a k ≠ 0 :=
        fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hck k))
      have key : ∀ k, Real.log (‖c y' k‖ / ‖c y k‖) = Real.log ‖c y' k‖ - Real.log ‖c y k‖ :=
        fun k => Real.log_div (norm_ne_zero_iff.mpr (hck k)) (norm_ne_zero_iff.mpr (hc0 k))
      have hb : (L j).h (bsmul (c y') (γ y')) = (∏ k, ‖c y' k‖ ^ (L j).a k) * (L j).h (γ y') :=
        (L j).smul _ _ hck
      simp only [pot]
      rw [h2, hb, Real.log_mul (Finset.prod_ne_zero_iff.mpr hne) hpos.ne',
        Real.log_prod hne]
      simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re, norm_div, key,
        Real.log_zpow, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [cxHessian_congr hev]
    exact cxHessian_add_re _ (pot_contDiffAt (hL j) hγ hy) hG
  simp only [maDensity, hj]

theorem sheet_analyticAt (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := _root_.mem_nhds_iff.mp (h.2.mono fun _ h' => h'.1)
  rw [analyticAt_pi_iff]
  intro p
  exact hA e U _ hUo (fun y' hy' => (differentiableAt_pi.mp (hU hy') p).differentiableWithinAt) y hyU

theorem sheetIndep_of (hA : OsgoodStatement) (hfib : FibreFiniteStatement) : SheetIndepStatement := by
  intro K _ ι _ P e Ψ L A s hvar hgood hL _ hs
  have hbad := badSet_null hA (hfib K ι P e Ψ hvar hgood)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbad] with y hy w γ γ' h h'
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y') := by
    by_contra hne
    exact hy ⟨w, γ, γ', h, h', hne⟩
  exact density_eq hL hs (sheet_analyticAt hA h) (sheet_analyticAt hA h') h.2.self_of_nhds.2.1.1 hseg

theorem sheetIndep : SheetIndepStatement := sheetIndep_of osgood fibreFinite

end ReciprocityTheory.ChartRestriction.G.Geo
