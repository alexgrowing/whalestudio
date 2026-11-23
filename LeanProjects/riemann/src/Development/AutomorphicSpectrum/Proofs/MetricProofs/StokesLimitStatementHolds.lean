import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTVb
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNbarLeviChartReg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtLogNorm
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisorStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMeasurableDominatingFunctionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModelStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2Statement

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.VbLimit

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def ReHolAt (A : FinHolAtlas e X) (f : X → ℝ) (y₀ : X) : Prop :=
  ∃ W : Set X, IsOpen W ∧ y₀ ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, f z = (G z).re

theorem holoOn_mono {A : FinHolAtlas e X} {U V : Set X} {G : X → ℂ} (h : A.HoloOn U G) (hVU : V ⊆ U) :
    A.HoloOn V G := fun j u hu => h j u ⟨hu.1, hVU hu.2⟩

theorem holoOn_continuousOn {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) :
    ContinuousOn f W := by
  intro z hz
  obtain ⟨j, hj⟩ := A.cover z
  have h1 : (A.chart j).symm (A.chart j z) = z := (A.chart j).left_inv hj
  have hu : A.chart j z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, h1]; exact hz⟩
  have hc : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j z) := (h j _ hu).continuousAt
  have hc2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) z :=
    ContinuousAt.comp hc ((A.chart j).continuousAt hj)
  have hev : ((f ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 z] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  exact (hc2.congr hev).continuousWithinAt

theorem ReHolAt.congr {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hg : ReHolAt A g y₀)
    (h : f =ᶠ[𝓝 y₀] g) : ReHolAt A f y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hg
  obtain ⟨T, hT, hTo, hyT⟩ := mem_nhds_iff.1 h
  exact ⟨W ∩ T, hW.inter hTo, ⟨hy, hyT⟩, G, holoOn_mono hG Set.inter_subset_left,
    fun z hz => (hT hz.2).trans (hWG z hz.1)⟩

theorem ReHolAt.add {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hf : ReHolAt A f y₀)
    (hg : ReHolAt A g y₀) : ReHolAt A (fun y => f y + g y) y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hf
  obtain ⟨W', hW', hy', G', hG', hWG'⟩ := hg
  refine ⟨W ∩ W', hW.inter hW', ⟨hy, hy'⟩, fun z => G z + G' z, fun j u hu => ?_, fun z hz => ?_⟩
  · exact (hG j u ⟨hu.1, hu.2.1⟩).add (hG' j u ⟨hu.1, hu.2.2⟩)
  · show f z + g z = (G z + G' z).re
    rw [hWG z hz.1, hWG' z hz.2, Complex.add_re]

theorem ReHolAt.const_mul {A : FinHolAtlas e X} {f : X → ℝ} {y₀ : X} (c : ℝ) (hf : ReHolAt A f y₀) :
    ReHolAt A (fun y => c * f y) y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hf
  refine ⟨W, hW, hy, fun z => (c : ℂ) * G z, fun j u hu => ?_, fun z hz => ?_⟩
  · exact analyticAt_const.mul (hG j u hu)
  · show c * f z = ((c : ℂ) * G z).re
    rw [hWG z hz, Complex.re_ofReal_mul]

theorem ReHolAt.sub {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hf : ReHolAt A f y₀)
    (hg : ReHolAt A g y₀) : ReHolAt A (fun y => f y - g y) y₀ := by
  refine (hf.add (hg.const_mul (-1))).congr (Eventually.of_forall fun y => ?_)
  show f y - g y = f y + -1 * g y
  ring

theorem ReHolAt.sum {A : FinHolAtlas e X} {J : Type} (s : Finset J) {f : J → X → ℝ} {y₀ : X}
    (hf : ∀ i ∈ s, ReHolAt A (f i) y₀) : ReHolAt A (fun y => ∑ i ∈ s, f i y) y₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j u _ => analyticAt_const, ?_⟩
    intro z _
    simp
  | insert a s ha ih =>
    refine ((hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr (Eventually.of_forall fun y => ?_)
    show ∑ i ∈ insert a s, f i y = f a y + ∑ i ∈ s, f i y
    rw [Finset.sum_insert ha]

theorem reHolAt_log_norm {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} {y₀ : X} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hy : y₀ ∈ W) (h0 : f y₀ ≠ 0) :
    ReHolAt A (fun y => Real.log ‖f y‖) y₀ := by
  have hS : IsOpen {w : ℂ | w / f y₀ ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (continuous_id.div_const _)
  have hW' := (holoOn_continuousOn hf).isOpen_inter_preimage hW hS
  refine ⟨_, hW', ⟨hy, ?_⟩, fun z => Complex.log (f z / f y₀) + (Real.log ‖f y₀‖ : ℂ),
    fun j u hu => ?_, fun z hz => ?_⟩
  · show f y₀ / f y₀ ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) u := hf j u ⟨hu.1, hu.2.1⟩
    exact ((h1.div_const (c := f y₀)).clog hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := fun h => by
      have := Complex.slitPlane_ne_zero hz.2
      simp [h] at this
    rw [Complex.add_re, Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0),
      Complex.ofReal_re]
    ring

end General

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

def IsSecOn (M : CxModel P d) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ) : Prop :=
  (∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧ ∀ p, M.atlas.HoloOn U fun y => s y p

theorem reHolAt_log_sections {M : CxModel P d} {U U' : Set M.Xc} {s s' : M.Xc → (Σ k, ι k) → ℂ}
    {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} (hU : IsOpen U) (hU' : IsOpen U') (hs : IsSecOn M U s)
    (hs' : IsSecOn M U' s')
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hpos : ∀ z ∈ mcPts P, 0 < F z) {y₀ : M.Xc} (hy : y₀ ∈ U) (hy' : y₀ ∈ U') :
    ReHolAt M.atlas (fun y => Real.log (F (s' y)) - Real.log (F (s y))) y₀ := by
  classical
  have hz := (hs.1 y₀ hy).1
  have hz' := (hs'.1 y₀ hy').1
  choose i hi using hz.1
  obtain ⟨c₀, hc₀, hcz⟩ := (M.fibre _ hz _ hz').1 (by rw [(hs.1 y₀ hy).2, (hs'.1 y₀ hy').2])
  have hi' : ∀ k, s' y₀ ⟨k, i k⟩ ≠ 0 := by
    intro k
    rw [hcz]
    exact mul_ne_zero (hc₀ k) (hi k)
  have hR : ∀ k ∈ (Finset.univ : Finset K), ReHolAt M.atlas
      (fun y => (a k : ℝ) * (Real.log ‖s' y ⟨k, i k⟩‖ - Real.log ‖s y ⟨k, i k⟩‖)) y₀ := fun k _ =>
    ((reHolAt_log_norm hU' (hs'.2 _) hy' (hi' k)).sub
      (reHolAt_log_norm hU (hs.2 _) hy (hi k))).const_mul _
  refine (ReHolAt.sum Finset.univ hR).congr ?_
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k, s y ⟨k, i k⟩ ≠ 0 := eventually_all.2 fun k =>
    ((holoOn_continuousOn (hs.2 ⟨k, i k⟩)).continuousAt (hU.mem_nhds hy)).eventually_ne (hi k)
  filter_upwards [hU.mem_nhds hy, hU'.mem_nhds hy', hev] with y h1 h2 h3
  have hm := (hs.1 y h1).1
  have hm' := (hs'.1 y h2).1
  obtain ⟨c, hc, hcy⟩ := (M.fibre _ hm _ hm').1 (by rw [(hs.1 y h1).2, (hs'.1 y h2).2])
  have hnc : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
  rw [hcy, hF _ hm c hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hnc k))
    (hpos _ hm).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hnc k)), add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h4 : torusSmul c (s y) ⟨k, i k⟩ = c k * s y ⟨k, i k⟩ := rfl
  rw [h4, Real.log_zpow, norm_mul, Real.log_mul (hnc k) (norm_ne_zero_iff.2 (h3 k)), add_sub_cancel_right]

end Model

section Component

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

theorem reHolAt_log_vert (D : ComponentData II Ψ K ι Ω E) {p' : ℕ} (hp : p' ∈ D.S) {M : XModel D}
    {U : Set M.Xc} {s : M.Xc → (Σ k, ι k) → ℂ} (hU : IsOpen U) (hs : IsSecOn M U s) {y₀ : M.Xc}
    (hy : y₀ ∈ U) : ReHolAt M.atlas (fun y => Real.log (D.vertFactor p' (s y))) y₀ := by
  obtain ⟨T, hTa, hT0, hTe⟩ :=
    GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChartReg.vertFactor_local D hp (hs.1 y₀ hy).1
  obtain ⟨O, hOs, hOo, hzO⟩ := mem_nhds_iff.1 (hTa.eventually_analyticAt.and hTe)
  have hsc : ContinuousOn s U := continuousOn_pi.2 fun p => holoOn_continuousOn (hs.2 p)
  have hW := hsc.isOpen_inter_preimage hU hOo
  have hf : M.atlas.HoloOn (U ∩ s ⁻¹' O) (fun y => T (s y)) := by
    intro j u hu
    have h1 : AnalyticAt ℂ (s ∘ (M.atlas.chart j).symm) u :=
      analyticAt_pi_iff.2 fun p => hs.2 p j u ⟨hu.1, hu.2.1⟩
    have h2 : AnalyticAt ℂ T ((s ∘ (M.atlas.chart j).symm) u) := (hOs hu.2.2).1
    exact h2.comp h1
  refine (reHolAt_log_norm hW hf ⟨hy, hzO⟩ hT0).congr ?_
  filter_upwards [hW.mem_nhds ⟨hy, hzO⟩] with y hy'
  rw [(hOs hy'.2).2 (hs.1 y hy'.1).1]

end Component

section HidaSetting

open GroundTheory.Heights₂.Heights.LowerBoundFree.MuRegSmooth GroundTheory.Heights₂.Heights.LowerBoundFree.TopNPoly
  GroundTheory.Heights₂.Heights.LowerBoundFree.NbarSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem log_nbarQ (X : ComponentSetting D O Lt) (B p q : ℕ) (hq : 1 ≤ q) (t : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (q : ℝ)⁻¹ * Real.log ((X.NbarQ B p q t).h z) =
      Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z) +
        ∑ p' ∈ D.SB B, Real.log (D.vertFactor p' z) + (p : ℝ) / q * Real.log (D.A'.h z) := by
  have hVS := VertFactorSmooth.proof VertFactorPos.proof
  set Pd := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg X.H B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z))) ^ q *
    (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hMH : IsMultiHomogIdeal Pd := D.arith.2.1.2.1
  have hvpos : ∀ z ∈ mcPts Pd, ∀ p' ∈ D.SB B, 0 < D.vertFactor p' z := fun z hz p' hp' =>
    VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') z hz
  have hpos : ∀ z ∈ mcPts Pd, 0 < F z := by
    intro z hz
    have h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z := Finset.prod_pos (hvpos z hz)
    exact mul_pos (mul_pos (pow_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q))
      (pow_pos (D.A'.pos z hz.1) p)
  have hhom : ∀ z ∈ mcPts Pd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts Pd := mcPts_smul hMH c hc hz
    have hproj : X.M.proj (torusSmul c z) = X.M.proj z := ((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z := by
      have := X.S.ref.smul c z hc
      rw [X.S.ref_deg] at this
      exact this
    have hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
      have := D.A'.smul c z hc
      rw [D.A'_deg] at this
      exact this
    have hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) =
        (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z :=
      fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).1 z hz c hc
    have hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg X.H B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p := by
      intro k
      have hx : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      have hak : a k = (q : ℤ) * (muTwDeg X.H B) k + (p : ℤ) * D.a' k := by
        simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hak, zpow_add₀ hx, zpow_mul', zpow_natCast, zpow_mul', zpow_natCast]
    have hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ X.H.aMu k) *
        ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p := by
      rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        muTwDeg, prod_norm_zpow_add_sum hc]
    simp only [hFdef]
    rw [hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]
    ring
  have hN : (X.NbarQ B p q t).h z = F z :=
    (smoothRep_h _ hz).trans (hermOfFun_h_of_mem hMH hhom hz (hpos z hz))
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := hq
    positivity
  have href := X.S.ref.pos z hz.1
  have hA := D.A'.pos z hz.1
  have hv0 : ∏ p' ∈ D.SB B, D.vertFactor p' z ≠ 0 := (Finset.prod_pos (hvpos z hz)).ne'
  have hX : (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z))) ^ q ≠ 0 :=
    (pow_pos (mul_pos href (Real.exp_pos _)) q).ne'
  have hY : (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q ≠ 0 := pow_ne_zero _ hv0
  have hZ : D.A'.h z ^ p ≠ 0 := (pow_pos hA p).ne'
  rw [hN]
  simp only [hFdef]
  rw [Real.log_mul (mul_ne_zero hX hY) hZ, Real.log_mul hX hY, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul href.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_prod (fun p' hp' => (hvpos z hz p' hp').ne')]
  field_simp

end HidaSetting

section Final

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem contDiffAt_two_pot {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  ((hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy)).of_le
    (WithTop.coe_le_coe.2 le_top)

theorem isPsh_shift {A : FinHolAtlas e X} {th Θ : LocPot X} {u : X → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hth : IsPotential A th) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hu : A.Smooth u)
    (hpsh : IsPsh A (th + LocPot.ofFun u + Θ.rsmul 1)) :
    IsPsh A (th + Θ.rsmul c + LocPot.ofFun u + Θ) := by
  intro x j y hy w
  have hpot : IsPotential A (th + LocPot.ofFun u + Θ.rsmul 1) :=
    isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A u hu)) (isPotentialRsmul A 1 Θ hΘ)
  have hUth : (A.chart j).symm y ∈ th.U x := hy.2.1.1.1
  have hUΘ : (A.chart j).symm y ∈ Θ.U x := hy.2.2
  have hy1 : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul 1).U x :=
    ⟨hy.1, ⟨hUth, Set.mem_univ _⟩, hUΘ⟩
  have hy2 : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hUΘ⟩
  have hfun : (th + Θ.rsmul c + LocPot.ofFun u + Θ).φ x ∘ (A.chart j).symm =
      fun v => ((th + LocPot.ofFun u + Θ.rsmul 1).φ x ∘ (A.chart j).symm) v +
        c * (Θ.φ x ∘ (A.chart j).symm) v := by
    funext v
    show th.φ x _ + c * Θ.φ x _ + u _ + Θ.φ x _ = th.φ x _ + u _ + 1 * Θ.φ x _ + c * Θ.φ x _
    ring
  rw [hfun, levi_add_smul c (contDiffAt_two_pot hpot x j hy1) (contDiffAt_two_pot hΘ x j hy2) w]
  have h1 := hpsh x j y hy1 w
  have h2 : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w := by
    by_cases hw : w = 0
    · subst hw
      simp [levi]
    · exact (hΘp x j y hy2 w hw).le
  exact add_nonneg h1 (mul_nonneg hc h2)

end Final

section Setting2

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem potential_nbarQ (X : ComponentSetting D O Lt) (Θ : LocPot X.M.Xc) (hs : ∀ x, ∀ y₀ ∈ (Θ).U x ∩ Set.univ,
      ∃ U : Set X.M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Θ).U x ∩ Set.univ ∧ ∃ s : X.M.Xc → (Σ k, ι k) → ℂ,
        (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (s y') = y') ∧
        (∀ p, X.M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : X.M.Xc → ℂ, X.M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, (Θ).φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re)
    (hYo : IsOpen X.S.R.Yo) (B p q : ℕ) (hq : 1 ≤ q) (t : ℝ) (x : X.M.Xc) (y₀ : X.M.Xc)
    (hy : y₀ ∈ (X.S.R.th + Θ.rsmul ((p : ℝ) / q) + LocPot.ofFun (X.S.regWeight t)).U x ∩ X.S.R.Yo) :
    ∃ U : Set X.M.Xc, IsOpen U ∧ y₀ ∈ U ∧
      U ⊆ (X.S.R.th + Θ.rsmul ((p : ℝ) / q) + LocPot.ofFun (X.S.regWeight t)).U x ∩ X.S.R.Yo ∧
      ∃ s : X.M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (s y') = y') ∧
        (∀ p, X.M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : X.M.Xc → ℂ, X.M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, (X.S.R.th + Θ.rsmul ((p : ℝ) / q) + LocPot.ofFun (X.S.regWeight t)).φ x y' -
            (fun z => (q : ℝ)⁻¹ * Real.log ((X.NbarQ B p q t).h z)) (s y') = (G y').re := by
  have hth : y₀ ∈ X.S.R.th.U x := hy.1.1.1
  have hΘy : y₀ ∈ Θ.U x := hy.1.1.2
  obtain ⟨U₁, hU₁, hy₁, hU₁s, s, hsm, hsH, G₁, hG₁, hr₁⟩ := X.S.th_ref x y₀ hth
  obtain ⟨U₂, hU₂, hy₂, hU₂s, s₂, hsm₂, hsH₂, G₂, hG₂, hr₂⟩ := hs x y₀ ⟨hΘy, Set.mem_univ _⟩
  have hsec : IsSecOn X.M U₁ s := ⟨hsm, hsH⟩
  have hsec₂ : IsSecOn X.M U₂ s₂ := ⟨hsm₂, hsH₂⟩
  have hA : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
    intro z _ c hc
    have := D.A'.smul c z hc
    rw [D.A'_deg] at this
    exact this
  have h1 : ReHolAt X.M.atlas (fun y => (G₁ y).re) y₀ :=
    ⟨U₁, hU₁, hy₁, G₁, hG₁, fun _ _ => rfl⟩
  have h2 : ReHolAt X.M.atlas (fun y => (G₂ y).re) y₀ :=
    ⟨U₂, hU₂, hy₂, G₂, hG₂, fun _ _ => rfl⟩
  have h3 := reHolAt_log_sections hU₁ hU₂ hsec hsec₂ hA (fun z hz => D.A'.pos z hz.1) hy₁ hy₂
  have h4 : ReHolAt X.M.atlas (fun y => ∑ p' ∈ D.SB B, Real.log (D.vertFactor p' (s y))) y₀ :=
    ReHolAt.sum _ fun p' hp' => reHolAt_log_vert D (Finset.mem_filter.1 hp').1 hU₁ hsec hy₁
  have hall := (h1.add ((h2.add h3).const_mul ((p : ℝ) / q))).sub h4
  obtain ⟨W, hW, hyW, G, hG, hWG⟩ := hall
  refine ⟨W ∩ (U₁ ∩ (U₂ ∩ X.S.R.Yo)), hW.inter (hU₁.inter (hU₂.inter hYo)), ⟨hyW, hy₁, hy₂, hy.2⟩, ?_, s,
    fun y' hy' => hsm y' hy'.2.1, fun p => holoOn_mono (hsH p) fun y' hy' => hy'.2.1, G,
    holoOn_mono hG Set.inter_subset_left, fun y' hy' => ?_⟩
  · intro y' hy'
    exact ⟨⟨⟨(hU₁s hy'.2.1 : _), (hU₂s hy'.2.2.1).1⟩, Set.mem_univ _⟩, hy'.2.2.2⟩
  · have hm := hsm y' hy'.2.1
    have e1 := hr₁ y' hy'.2.1
    have e2 := hr₂ y' hy'.2.2.1
    rw [← hWG y' hy'.1]
    show X.S.R.th.φ x y' + (p : ℝ) / q * Θ.φ x y' + X.S.regWeight t y' -
      (q : ℝ)⁻¹ * Real.log ((X.NbarQ B p q t).h (s y')) = _
    rw [log_nbarQ X B p q hq t hm.1, hm.2]
    simp only at e2 ⊢
    rw [← e1, ← e2]
    ring

end Setting2

section Top

open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem stokesLimitTVb : StokesLimitTVb.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp hpq
  classical
  have hq : 1 ≤ q := hp.trans hpq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hΨ : ∃ Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ), IsGoodProj (mCoordIdeal D.y) Q
  swap
  · refine ⟨0, ?_⟩
    have h0 : X.Vb B p q = fun _ => 0 := by
      funext t
      unfold ComponentSetting.Vb ptsIntegral
      rw [dif_neg hΨ]
    rw [h0]
    exact tendsto_const_nhds
  obtain ⟨Θ, hΘ, hΘs⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K ι (mCoordIdeal D.y) D.n X.M D.A' D.A'_pos.1
  have hΘp : IsPosPot X.M.atlas Θ := GlobalTheory.T.local_section_of_potential_on_model II Ψ K ι Ω E D X.M Θ hΘ hΘs
  obtain ⟨-, ⟨C₁, hC₁⟩, hε⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S Θ X.S_tied hΘ hΘp
  obtain ⟨hYo, hnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties D.n X.M.Xc X.M.atlas X.S.R
  obtain ⟨G, Cg, hGm, hGb, hGe⟩ := GlobalTheory.T.cuspWeight_factors_through_measurable_log_bounded II Ψ K ι Ω E D O Lt X
  set R := X.S.R with hR
  set c : ℝ := (p : ℝ) / q with hc
  have hc0 : 0 ≤ c := by positivity
  set Pp : LocPot X.M.Xc := R.th + Θ.rsmul c with hPp
  have hPpot : IsPotential X.M.atlas Pp := isPotentialAdd _ _ _ R.th_pot (isPotentialRsmul _ c Θ hΘ)
  set G₀ : X.M.Xc → ℝ := fun x => R.Yo.indicator G x / 2 with hG₀
  have hG₀Yo : ∀ x ∈ R.Yo, G₀ x = G x / 2 := fun x hx => by
    simp only [hG₀, Set.indicator_of_mem hx]
  have hlog : ∀ x ∈ R.Yo, 0 ≤ Real.log (R.r x) := fun x hx => Real.log_nonneg (R.one_le_r x hx)
  set C : ℝ := |C₁| + |R.Clog| + |Cg| with hCdef
  have hC1 : |C₁| ≤ C := by
    have := abs_nonneg R.Clog
    have := abs_nonneg Cg
    simp only [hCdef]
    linarith
  have hC2 : |R.Clog| ≤ C := by
    have := abs_nonneg C₁
    have := abs_nonneg Cg
    simp only [hCdef]
    linarith
  have hC3 : |Cg| ≤ C := by
    have := abs_nonneg C₁
    have := abs_nonneg R.Clog
    simp only [hCdef]
    linarith
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hC1
  have hconv := GlobalTheory.T.mixed_integral_tendsto_off_divisor D.n X.M.Xc X.M.atlas R Θ hΘ hΘp (fun _ => Pp) (fun _ => R.ph)
    (fun _ t => X.S.regWeight t) G₀ (fun _ => G₀) C (fun _ => hPpot) (fun _ => R.ph_smooth) ?_ ?_ ?_ ?_
  · obtain ⟨-, hMI, hT⟩ := hconv
    refine ⟨_, hT.congr' ?_⟩
    filter_upwards [hMI, hC₁] with t hMIt hC₁t
    obtain ⟨hsm, -⟩ := hC₁t
    have hpush := GlobalTheory.T.mixed_integral_model_formula K ι (mCoordIdeal D.y) D.n X.M hΨ.choose R.Yo ∅ ∅ (fun _ => (q : ℝ)⁻¹)
      (fun _ => X.NbarQ B p q t) (fun _ => Pp + LocPot.ofFun (X.S.regWeight t))
      (fun z => X.Cd.cuspWeight z / 2) G₀ D.arith hΨ.choose_spec hYo
      (fun j => by simpa using (hnull j))
      (fun Ψ' _ => by simp)
      (fun _ x => fun j => ((isPotentialAdd _ _ _ hPpot (isPotential_ofFun _ _ hsm)).1 x j).mono
        fun u hu => ⟨hu.1, hu.2.1⟩)
      (fun _ x y₀ hy => potential_nbarQ X Θ hΘs hYo B p q hq t x y₀ hy)
      (fun z hz _ hzY _ => by
        show X.Cd.cuspWeight z / 2 = G₀ (X.M.proj z)
        rw [hG₀Yo _ hzY, hGe z hz hzY])
      ?_
    · have hVb : X.Vb B p q t = ptsIntegralAt (mCoordIdeal D.y) hΨ.choose
          (fun _ z => (q : ℝ)⁻¹ * Real.log ((X.NbarQ B p q t).h z)) (fun z => X.Cd.cuspWeight z / 2) := by
        unfold ComponentSetting.Vb ptsIntegral
        rw [dif_pos hΨ]
        congr 1
        funext _ z
        simp only [ComponentSetting.omN]
        rw [div_eq_inv_mul]
      rw [hVb]
      exact ((hpush.2.2 hMIt).2).symm
    · intro j
      letI : MeasurableSpace X.M.Xc := borel X.M.Xc
      haveI : BorelSpace X.M.Xc := ⟨rfl⟩
      have h1 : AEMeasurable (X.M.atlas.chart j).symm (volume.restrict (X.M.atlas.chart j).target) :=
        (X.M.atlas.chart j).continuousOn_symm.aemeasurable (X.M.atlas.chart j).open_target.measurableSet
      have h2 : Measurable G₀ := (by fun_prop : Measurable fun v : ℝ => v / 2).comp hGm
      exact (h2.comp_aemeasurable h1).aestronglyMeasurable
  · filter_upwards [hC₁, hε 1 one_pos] with t ht hpsh i
    obtain ⟨hsm, hb⟩ := ht
    refine ⟨hsm, isPsh_shift hc0 R.th_pot hΘ hΘp hsm hpsh, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hb x hx
    have h3 := R.ph_ge x hx
    have hl := hlog x hx
    have hle : X.S.regWeight t x ≤ C := h2.trans ((le_abs_self _).trans hC1)
    refine ⟨abs_le.2 ⟨?_, ?_⟩, hle⟩
    · have : -(R.Clog * Real.log (R.r x)) ≥ -(C * Real.log (R.r x)) := by
        have := mul_le_mul_of_nonneg_right ((le_abs_self _).trans hC2) hl
        linarith
      nlinarith
    · have := mul_nonneg hC0 hl
      linarith
  · intro i j K' hK' hc'
    exact GlobalTheory.T.regularized_weight_tendsto_C2 K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S X.S_tied j K' hK' hc'
  · refine Eventually.of_forall fun t => ⟨?_, fun x hx => ?_⟩
    · have hind : R.Yo.indicator G₀ = G₀ := by
        funext x
        by_cases hx : x ∈ R.Yo
        · simp [hx]
        · simp [hx, hG₀]
      show @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (R.Yo.indicator G₀)
      rw [hind]
      exact (by fun_prop : Measurable fun v : ℝ => v / 2).comp hGm
    · show |G₀ x| ≤ C + C * Real.log (R.r x)
      rw [hG₀Yo x hx, abs_div, abs_two]
      have h1 := hGb x hx
      have hl := hlog x hx
      have h2 : Cg * Real.log (R.r x) ≤ C * Real.log (R.r x) :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans hC3) hl
      have h3 : Cg ≤ C := (le_abs_self _).trans hC3
      have h4 := abs_nonneg (G x)
      have h5 := mul_nonneg hC0 hl
      linarith
  · intro K' _ _
    exact fun u hu => Eventually.of_forall fun t x _ => by simpa using mem_uniformity_of_eq hu rfl

end Top

end GlobalTheory.CompanionTheory.Ar.Giv.VbLimit
