import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LojasiewiczInequalityAnalyticStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Decay

open Filter Topology

theorem analyticAt_aeval {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : E → σ → ℂ} {z : E}
    (hv : ∀ p, AnalyticAt ℂ (fun w => v w p) z) (q : MvPolynomial σ ℤ) :
    AnalyticAt ℂ (fun w => (aeval (v w) q : ℂ)) z := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, aeval_X]
    exact hp.mul (hv i)

theorem continuousAt_of_chart {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
    (c : OpenPartialHomeomorph X E) {x : X} (hx : x ∈ c.source) {F : X → Y}
    (h : ContinuousAt (fun z => F (c.symm z)) (c x)) : ContinuousAt F x := by
  have h1 : ContinuousAt (fun y => F (c.symm (c y))) x :=
    ContinuousAt.comp (f := c) (g := fun z => F (c.symm z)) h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  rw [c.left_inv hy]

theorem isOpen_multicone {K : Type*} [Finite K] {ι : K → Type*} :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem eventually_abs_le {X : Type*} [TopologicalSpace X] {u : X → ℝ} {x : X} (h : ContinuousAt u x) :
    ∀ᶠ y in 𝓝 x, |u y| ≤ |u x| + 1 :=
  (h.abs.eventually_lt (continuousAt_const (y := |u x| + 1)) (by linarith)).mono fun _ hy => hy.le

theorem section_zero {e : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {x x' y : X} (hy : y ∈ L.U x ∩ L.U x') (h0 : s x y = 0) :
    s x' y = 0 := by
  have h := hs.2 x x' y hy
  rw [h0, norm_zero, zero_mul] at h
  exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_ne_zero _))

theorem logNormSec_eq {e : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {x y : X} (hy : y ∈ L.U x) (h0 : s x y ≠ 0) :
    logNormSec L s y = Real.log ‖s x y‖ - L.φ x y := by
  unfold logNormSec
  rw [hs.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.2 h0) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem log_ratio_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (Eh : HermLine ι)
    {dg dh : K → ℕ} {G Hf : MRing ι} (hG : IsMultiHomog G dg) (hH : IsMultiHomog Hf dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + Eh.a k) (t : K → ℂ) (ht : ∀ k, t k ≠ 0) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hGw : aeval w G ≠ (0 : ℂ)) (hHw : aeval w Hf ≠ (0 : ℂ)) :
    Real.log ‖(aeval w G : ℂ) / aeval w Hf‖ - Real.log (Eh.h w) =
      Real.log ‖(aeval (fun p => t p.1 * w p) G : ℂ) / aeval (fun p => t p.1 * w p) Hf‖ -
        Real.log (Eh.h fun p => t p.1 * w p) := by
  rw [aeval_scale hG, aeval_scale hH, Eh.smul t w ht]
  have hT : 0 < ∏ k, ‖t k‖ ^ Eh.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (ht k)) _
  have hP : ‖∏ k, t k ^ dg k‖ = ‖∏ k, t k ^ dh k‖ * ∏ k, ‖t k‖ ^ Eh.a k := by
    simp only [norm_prod, norm_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, hdeg k, zpow_add₀ (norm_ne_zero_iff.2 (ht k)), zpow_natCast]
  have hPh : ‖∏ k, t k ^ dh k‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k))
  have hn : ‖((∏ k, t k ^ dg k) * aeval w G : ℂ) / ((∏ k, t k ^ dh k) * aeval w Hf)‖ =
      (∏ k, ‖t k‖ ^ Eh.a k) * ‖(aeval w G : ℂ) / aeval w Hf‖ := by
    rw [norm_div, norm_mul, norm_mul, hP, norm_div]
    field_simp
  have hq : ‖(aeval w G : ℂ) / aeval w Hf‖ ≠ 0 := norm_ne_zero_iff.2 (div_ne_zero hGw hHw)
  rw [hn, Real.log_mul hT.ne' hq, Real.log_mul hT.ne' (Eh.pos w hw).ne']
  ring

theorem decay_arith {N : ℕ} (hN : 0 < N) {Lf lh lg φ lC Bh Bφ : ℝ} (h1 : (N : ℝ) * Lf ≤ lC + lg)
    (h2 : |lh| ≤ Bh) (h3 : |φ| ≤ Bφ) :
    Lf - lh ≤ -(1 / (2 * (N : ℝ))) * (Real.exp 1 - 2 * (lg - φ)) +
      ((lC + Real.exp 1 / 2 + Bφ) / (N : ℝ) + Bh) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have e1 : Lf ≤ (lC + lg) / N := by
    rw [le_div_iff₀ hn]
    linarith
  have e2 : -(1 / (2 * (N : ℝ))) * (Real.exp 1 - 2 * (lg - φ)) + (lC + Real.exp 1 / 2 + Bφ) / N =
      (lC + lg) / N + (Bφ - φ) / N := by
    field_simp
    ring
  have e3 : 0 ≤ (Bφ - φ) / N := div_nonneg (by linarith [le_abs_self φ]) hn.le
  have e4 : -lh ≤ Bh := by linarith [neg_abs_le lh]
  linarith

theorem local_decay : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → (∀ y : R.X, aeval (R.lift y y) G ≠ (0 : ℂ) → aeval (R.lift y y) Hf ≠ (0 : ℂ) → π y ∈ S.open') → ∀ x₀ : R.X, aeval (R.lift x₀ x₀) Hf ≠ (0 : ℂ) → ∃ (V : Set R.X) (N : ℕ) (C : ℝ), IsOpen V ∧ x₀ ∈ V ∧ 0 < N ∧ ∀ y ∈ V, aeval (R.lift y y) Hf ≠ (0 : ℂ) ∧ (π y ∈ S.open' → aeval (R.lift y y) G ≠ (0 : ℂ) → Real.log ‖(aeval (R.lift y y) G : ℂ) / aeval (R.lift y y) Hf‖ - Real.log (Eh.h (R.lift y y)) ≤ -(1 / (2 * (N : ℝ))) * rW S.L S.s (π y) + C) := by
  intro K _ ι _ P J e R σ S π hπ Eh hEh dg dh G Hf hG hH hdeg hyp x₀ hx₀
  obtain ⟨j, hj⟩ := R.A.cover x₀
  obtain ⟨k, hk⟩ := S.A.cover (π x₀)
  have hz₀ : (R.A.chart j).symm (R.A.chart j x₀) = x₀ := (R.A.chart j).left_inv hj
  have hd₀ : (S.A.chart k).symm (S.A.chart k (π x₀)) = π x₀ := (S.A.chart k).left_inv hk
  have hcoord : ∀ p, AnalyticAt ℂ (fun z => R.lift x₀ ((R.A.chart j).symm z) p) (R.A.chart j x₀) := fun p =>
    R.holo x₀ p j _ ⟨(R.A.chart j).map_source hj, by
      show (R.A.chart j).symm (R.A.chart j x₀) ∈ R.U x₀
      rw [hz₀]; exact R.mem_U x₀⟩
  have hGa := analyticAt_aeval hcoord G
  have hHa := analyticAt_aeval hcoord Hf
  have hHc : ContinuousAt (fun y => (aeval (R.lift x₀ y) Hf : ℂ)) x₀ :=
    continuousAt_of_chart (R.A.chart j) hj hHa.continuousAt
  have hne : ∀ᶠ y in 𝓝 x₀, (aeval (R.lift x₀ y) Hf : ℂ) ≠ 0 := hHc.eventually_ne hx₀
  have hU : ∀ᶠ y in 𝓝 x₀, y ∈ R.U x₀ := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
  have hS : ∀ᶠ y in 𝓝 x₀, y ∈ (R.A.chart j).source := (R.A.chart j).open_source.mem_nhds hj
  have hπc : ContinuousAt π x₀ := hπ.1.continuousAt
  have hπU : ∀ᶠ y in 𝓝 x₀, π y ∈ S.L.U (π x₀) :=
    hπc.eventually_mem ((S.L.isOpen_U _).mem_nhds (S.L.mem_U _))
  have hπk : ∀ᶠ y in 𝓝 x₀, π y ∈ (S.A.chart k).source :=
    hπc.eventually_mem ((S.A.chart k).open_source.mem_nhds hk)
  have tend : Tendsto (R.A.chart j).symm (𝓝 (R.A.chart j x₀)) (𝓝 x₀) := by
    have h := (R.A.chart j).continuousAt_symm ((R.A.chart j).map_source hj)
    rwa [ContinuousAt, hz₀] at h

  let f : (Fin e → ℂ) → ℂ := fun z =>
    (aeval (R.lift x₀ ((R.A.chart j).symm z)) G : ℂ) / aeval (R.lift x₀ ((R.A.chart j).symm z)) Hf
  let g : (Fin e → ℂ) → ℂ := fun z => S.s (π x₀) (π ((R.A.chart j).symm z))
  have hf : AnalyticAt ℂ f (R.A.chart j x₀) := hGa.div hHa (by simpa only [hz₀] using hx₀)
  have hg : AnalyticAt ℂ g (R.A.chart j x₀) := by
    have h1 : AnalyticAt ℂ ((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀) :=
      hπ.2 j k _ ⟨(R.A.chart j).map_source hj, by
        show π ((R.A.chart j).symm (R.A.chart j x₀)) ∈ (S.A.chart k).source
        rw [hz₀]; exact hk⟩
    have h2 : AnalyticAt ℂ (S.s (π x₀) ∘ (S.A.chart k).symm)
        (((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀)) := by
      have e1 : ((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀) = S.A.chart k (π x₀) := by
        simp only [Function.comp_apply, hz₀]
      rw [e1]
      exact S.sec.1 (π x₀) k _ ⟨(S.A.chart k).map_source hk, by
        show (S.A.chart k).symm (S.A.chart k (π x₀)) ∈ S.L.U (π x₀)
        rw [hd₀]; exact S.L.mem_U _⟩
    refine (h2.comp h1).congr ?_
    filter_upwards [tend.eventually hπk] with z hz
    simp only [Function.comp_apply, g, (S.A.chart k).left_inv hz]

  have hzero : ∀ᶠ z in 𝓝 (R.A.chart j x₀), g z = 0 → f z = 0 := by
    filter_upwards [tend.eventually hU, tend.eventually hπU, tend.eventually hne] with z h1 h2 h3 h0
    obtain ⟨t, ht, hlt⟩ := R.compat x₀ _ _ ⟨h1, R.mem_U ((R.A.chart j).symm z)⟩
    have hs := section_zero S.sec (x := π x₀) (x' := π ((R.A.chart j).symm z))
      ⟨h2, S.L.mem_U _⟩ h0
    have hHy : (aeval (R.lift ((R.A.chart j).symm z) ((R.A.chart j).symm z)) Hf : ℂ) ≠ 0 := by
      intro h00
      apply h3
      rw [hlt, aeval_scale hH, h00, mul_zero]
    have hGy : (aeval (R.lift ((R.A.chart j).symm z) ((R.A.chart j).symm z)) G : ℂ) = 0 := by
      by_contra hG0
      exact hyp _ hG0 hHy hs
    show (aeval (R.lift x₀ ((R.A.chart j).symm z)) G : ℂ) / _ = 0
    rw [hlt, aeval_scale hG, hGy, mul_zero, zero_div]
  obtain ⟨N, C₀, hN, hloj⟩ := GlobalTheory.T.lojasiewicz_inequality_analytic e f g _ hf hg hzero
  have hloj' : ∀ᶠ y in 𝓝 x₀, ‖f (R.A.chart j y)‖ ^ N ≤ C₀ * ‖g (R.A.chart j y)‖ :=
    ((R.A.chart j).continuousAt hj).eventually hloj

  have hφc : ContinuousAt (S.L.φ (π x₀)) (π x₀) :=
    continuousAt_of_chart (S.A.chart k) hk
      (((S.potL.1 (π x₀) k).continuousOn).continuousAt
        (((S.A.chart k).isOpen_inter_preimage_symm (S.L.isOpen_U _)).mem_nhds
          ⟨(S.A.chart k).map_source hk, by
            show (S.A.chart k).symm (S.A.chart k (π x₀)) ∈ S.L.U (π x₀)
            rw [hd₀]; exact S.L.mem_U _⟩))
  have hφb := eventually_abs_le (u := fun y => S.L.φ (π x₀) (π y)) (ContinuousAt.comp (g := S.L.φ (π x₀)) hφc hπc)
  have hℓ : ContinuousAt (fun y => R.lift x₀ y) x₀ :=
    continuousAt_pi.2 fun p => continuousAt_of_chart (R.A.chart j) hj (hcoord p).continuousAt
  have hmem : R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := (R.mem x₀ x₀ (R.mem_U x₀)).1
  have hhc : ContinuousAt Eh.h (R.lift x₀ x₀) :=
    (ContDiffOn.continuousOn hEh).continuousAt (isOpen_multicone.mem_nhds hmem)
  have hlogc : ContinuousAt (fun y => Real.log (Eh.h (R.lift x₀ y))) x₀ :=
    ContinuousAt.log (ContinuousAt.comp (g := Eh.h) hhc hℓ) (Eh.pos _ hmem).ne'
  have hhb := eventually_abs_le hlogc
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.1
    (hU.and (hS.and (hπU.and (hne.and (hloj'.and (hφb.and hhb))))))
  refine ⟨V, N, (Real.log (max C₀ 1) + Real.exp 1 / 2 + (|S.L.φ (π x₀) (π x₀)| + 1)) / (N : ℝ) +
    (|Real.log (Eh.h (R.lift x₀ x₀))| + 1), hVo, hxV, hN, fun y hy => ?_⟩
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := hV y hy
  obtain ⟨t, ht, hlt⟩ := R.compat x₀ y y ⟨y1, R.mem_U y⟩
  have hw : ∀ k, ∃ i, R.lift y y ⟨k, i⟩ ≠ 0 := (R.mem y y (R.mem_U y)).1
  have hHy : (aeval (R.lift y y) Hf : ℂ) ≠ 0 := by
    intro h00
    apply y4
    rw [hlt, aeval_scale hH, h00, mul_zero]
  refine ⟨hHy, fun hop hGy => ?_⟩
  have hs : S.s (π y) (π y) ≠ 0 := hop
  have hgne : S.s (π x₀) (π y) ≠ 0 := fun h0 => hs (section_zero S.sec ⟨y3, S.L.mem_U _⟩ h0)
  have hGl : (aeval (R.lift x₀ y) G : ℂ) ≠ 0 := by
    rw [hlt, aeval_scale hG]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hGy
  have hfy : f (R.A.chart j y) = (aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf := by
    simp only [f, (R.A.chart j).left_inv y2]
  have hgy : g (R.A.chart j y) = S.s (π x₀) (π y) := by
    simp only [g, (R.A.chart j).left_inv y2]
  rw [hfy, hgy] at y5
  have hfne : (aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf ≠ 0 := div_ne_zero hGl y4
  have key := log_ratio_scale Eh hG hH hdeg t ht (R.lift y y) hw hGy hHy
  rw [← hlt] at key
  rw [key, rW, logNormSec_eq S.sec y3 hgne]
  have hloglog : (N : ℝ) * Real.log ‖(aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf‖ ≤
      Real.log (max C₀ 1) + Real.log ‖S.s (π x₀) (π y)‖ := by
    have hC : 0 < max C₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hgp : 0 < ‖S.s (π x₀) (π y)‖ := norm_pos_iff.2 hgne
    have hle : ‖(aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf‖ ^ N ≤
        max C₀ 1 * ‖S.s (π x₀) (π y)‖ :=
      y5.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgp.le)
    have := Real.log_le_log (pow_pos (norm_pos_iff.2 hfne) N) hle
    rwa [Real.log_pow, Real.log_mul hC.ne' hgp.ne'] at this
  exact decay_arith hN hloglog y7 y6

end GlobalTheory.CompanionTheory.Ar.Small.Decay
