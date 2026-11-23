import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.ChernIso

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {A B : LB X} {φ : Weight p σ B} {D : ℕ}

theorem cInfAt_log_normSq {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (h0 : ev p σ W g y ≠ 0) : CInfAt (fun z => Real.log (‖ev p σ W g z‖ ^ 2)) y := by
  have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ ℂ ()).norm_sq ℂ
  refine ⟨W, Unit, inferInstance, fun _ => g, fun v => Real.log (‖v ()‖ ^ 2),
    {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const,
    pow_ne_zero _ (norm_ne_zero_iff.2 h0), hs.contDiffOn.log fun _ h => h, EventuallyEq.rfl⟩

theorem ofIso_apply (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) {a : A.ι} {b : B.ι}
    {y : CxPts p σ} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (φ.ofIso hA w hw).φ a y = φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2) := by
  rw [Weight.ofIso, Weight.ofPairs_φ ha hb]

theorem isCInf_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) :
    (φ.ofIso hA w hw).IsCInf := fun a y ha => by
  have hb := mem_pick φ.isLB y
  refine ((h _ y hb).add (cInfAt_log_normSq (w.s (a, pick φ.isLB y)).val
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (ev_iso_ne_zero w hb ha))).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds ha, (isOpen_ptsIn _).mem_nhds hb] with z h₁ h₂
  exact ofIso_apply hA w hw h₁ h₂

theorem hess_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) {a : A.ι} {b : B.ι}
    (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (φ.ofIso hA w hw) a y = c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo (A.U a ⊓ B.U b) (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (A.U a ⊓ B.U b),
      (ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 := fun v hv =>
    ev_iso_ne_zero w (mem_ptsIn_inf.1 hv.2).2 (mem_ptsIn_inf.1 hv.2).1
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘
      c.e.symm) v‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0 := by
    ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 i j
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ofIso_apply hA w hw (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem chernPart_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) (ε : ℤˣ) :
    (φ.ofIso hA w hw).chernPart D ε = φ.chernPart D ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun (measurableSet_image c.e
    (c.e.open_source.measurableSet.inter hS) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1]
  rw [AlgChart.chernDens, AlgChart.chernDens,
    hess_ofIso h hA w hw c hy.1 (mem_pick _ y) (mem_pick φ.isLB y)]

theorem chernInt_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (φ.ofIso hA w hw).chernInt D S f = φ.chernInt D S f := by
  rw [Weight.chernInt, Weight.chernInt, chernPart_ofIso h, chernPart_ofIso h]

theorem chernMass_ofIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧
      Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) =
        Weight.chernInt φ Y.dim Set.univ (fun _ => 1) :=
  fun _ _ _ _ hA w hw h => ⟨isCInf_ofIso h hA w hw, chernInt_ofIso h hA w hw _ _⟩

end GlobalTheory.ChernIso
