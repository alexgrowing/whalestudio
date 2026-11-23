import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackIsPotentialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNullStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatioStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPointStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
open Set Filter Topology

namespace GlobalTheory.CompanionTheory.MixZ

theorem lintegral_logNorm_locDens_lt_top : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B C : LB X} (φ : GlobalTheory.Weight q σ B) (_ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (_ : ψ.IsCInf)
      (g : GlobalTheory.CxPts q σ → ℝ) (S Z : Set (GlobalTheory.CxPts q σ)) {N : ℕ} (W : Fin N → X.Opens) (b : Fin N → C.ι)
      (a d : ∀ l, Γ(X, W l)),
    (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) → (∀ l, W l ≤ C.U (b l)) →
    (∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ S → y ∉ Z →
      g y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2) →
    IsOpen S → ContinuousOn g S → MeasurableSet Z →
    ∀ (j : Fin A.n) (K : Set (Fin D → ℂ)), K ⊆ (A.chart j).target → IsCompact K →
      ∫⁻ u in K \ (F ∘ (A.chart j).symm) ⁻¹' Z, S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤ := by
  intro k _ X q σ D T _ A F hF hol B C φ hφ ψ hψ g S Z N W b a d hcov hWb hg hSo hgc hZ j K hKt hKc
  have hGc : ContinuousOn (F ∘ (A.chart j).symm) (A.chart j).target :=
    hF.comp_continuousOn (A.chart j).continuousOn_symm
  have hdc : ContinuousOn (locDens A (fun _ => φ.locPot.pullback F hF) j) (A.chart j).target :=
    locDensCont A _ (fun _ => isPotential_pullback_locPot A F hF hol φ hφ) j
  refine hKc.induction_on (p := fun s => ∫⁻ u in s \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤) ?_ ?_ ?_ ?_
  · simp
  · intro s t hst ht
    exact (lintegral_mono_set (diff_subset_diff_left hst)).trans_lt ht
  · intro s t hs ht
    rw [union_diff_distrib]
    exact (lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)
  intro u0 hu0
  obtain ⟨l, hl⟩ := hcov (F ((A.chart j).symm u0))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l))) :=
    (A.chart j).isOpen_inter_preimage_symm ((isOpen_ptsIn _).preimage hF)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 ⟨hKt hu0, hl⟩
  set V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l)) with hV
  set Bl := Metric.closedBall u0 (r / 2) with hBl
  have hBV : Bl ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact Bl := isCompact_closedBall _ _
  have hBm : MeasurableSet Bl := Metric.isClosed_closedBall.measurableSet
  have hBt : Bl ⊆ (A.chart j).target := hBV.trans inter_subset_left
  refine ⟨Bl, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  have hla : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (a l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (a l) j u hu)).integrableOn_compact_subset hBV hBc
  have hld : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (d l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (d l) j u hu)).integrableOn_compact_subset hBV hBc
  have hψc : ContinuousOn (fun u => ψ.φ (b l) (F ((A.chart j).symm u))) Bl := by
    intro u hu
    have hc : ContinuousAt (ψ.φ (b l)) (F ((A.chart j).symm u)) :=
      (hψ (b l) _ (ptsIn_mono (hWb l) (hBV hu).2)).continuousAt
    exact ContinuousAt.comp_continuousWithinAt (f := F ∘ (A.chart j).symm) hc
      ((hGc u (hBt hu)).mono hBt)
  have hlψ : IntegrableOn (fun u => |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hψc.abs.div_const 2).integrableOn_compact hBc
  have hh : IntegrableOn (fun u => |Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
      |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
      |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hla.abs.add hld.abs).add hlψ
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn (hdc.mono hBt)
  have hYm : MeasurableSet (Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z) := by
    have hc : Continuous (fun u : Bl => (F ∘ (A.chart j).symm) u.1) :=
      continuousOn_iff_continuous_restrict.1 (hGc.mono hBt)
    have h1 : MeasurableSet (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) :=
      hBm.subtype_image (hc.measurable hZ)
    have h2 : Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z =
        Bl \ (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) := by
      ext u
      constructor
      · rintro ⟨hu, hn⟩
        refine ⟨hu, ?_⟩
        rintro ⟨v, hv, rfl⟩
        exact hn hv
      · rintro ⟨hu, hn⟩
        exact ⟨hu, fun hz => hn ⟨⟨u, hu⟩, hz, rfl⟩⟩
    rw [h2]
    exact hBm.diff h1
  have hpt : ∀ u ∈ Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| ≤
      ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
        |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
        |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M := by
    rintro u ⟨huB, huZ⟩
    by_cases hS : F ((A.chart j).symm u) ∈ S
    · rw [indicator_of_mem hS]
      refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_)
      · rw [← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hg l _ (hBV huB).2 hS huZ, Real.norm_eq_abs]
        have h1 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖ -
          Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
          (ψ.φ (b l) (F ((A.chart j).symm u)) / 2)
        have h2 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖)
          (Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
        rw [abs_div, abs_two] at h1
        linarith
      · simpa using hM u huB
    · rw [indicator_of_notMem hS, zero_mul]
      exact zero_le
  calc ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
          ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|
      ≤ ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        setLIntegral_mono' hYm hpt
    _ ≤ ∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        lintegral_mono_set diff_subset
    _ = (∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2)) * ENNReal.ofReal M :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top hh.lintegral_lt_top ENNReal.ofReal_lt_top

end GlobalTheory.CompanionTheory.MixZ
