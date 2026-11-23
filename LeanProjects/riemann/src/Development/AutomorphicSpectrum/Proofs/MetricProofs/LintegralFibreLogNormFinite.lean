import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSemiPosMassFinite
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProjStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableChartAbsDensityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ZeroSetChartIdealEqChartSetStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimChartComponentsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartComponentsFiniteProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartSectionNotMemComponentsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinateStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableDomCellLogNormChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DomCellLogNormMeasurableInvariantStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothMetricsNonnegDensityStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

section Assembly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem setSheetDensity_eq_zero {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ S, g z = 0) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : setSheetDensity S Ψ φ g y w = 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
  · rfl

theorem setSheetDensity_sum {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {τ : Type*} (t : Finset τ) (G : τ → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    setSheetDensity S Ψ φ (fun z => ∑ i ∈ t, G i z) y w = ∑ i ∈ t, setSheetDensity S Ψ φ (G i) y w := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
  · simp

theorem exists_mem_domCell [DecidableEq K] {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) :
    ∃ i, z ∈ domCell i := by
  choose i1 _ using hz
  have : Nonempty ((k : K) → ι k) := ⟨i1⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun i' : (k : K) → ι k => ‖segre z i'‖
  exact ⟨i, hi⟩

theorem segre_ne_zero_of_mem_domCell {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0)
    {i : (k : K) → ι k} (hi : z ∈ domCell i) : segre z i ≠ 0 := by
  choose i1 hi1 using hz
  have h1 : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hi1 k
  intro h0
  have := hi i1
  rw [h0, norm_zero] at this
  exact h1 (norm_le_zero_iff.1 this)

end Assembly

theorem cell_mass_lt_top {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {N : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) (hsQ : s ∉ Q)
    (hnn : ∀ y w, 0 ≤ setSheetDensity (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y w) :
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y) < ⊤ := by
  classical
  set σ : Fin (Fintype.card ((k : K) → ι k)) ≃ ((k : K) → ι k) := (Fintype.equivFin _).symm with hσ
  set G := (domCell i).indicator (absLogNorm A s) with hG
  obtain ⟨hGm, hGi⟩ := GlobalTheory.T.domCell_logNorm_measurable_invariant K ι A s a i hA hAa hs
  have hzero := GlobalTheory.T.zeroSet_chartIdeal_eq_chartSet K ι Q _ σ i hQ.2.1.2.1
  have hdim := GlobalTheory.T.ringKrullDim_chartComponents K ι Q e _ σ i hQ
  have hfin := GlobalTheory.T.chartComponents_finite_projection K ι Q e _ σ i Ψ hQ hΨ hΨ0 hdim
  have hfs := GlobalTheory.T.chart_density_integrable K ι Q e _ σ i N G Ψ hQ hN hGi hΨ0 (GlobalTheory.T.setFibre_finite_of_goodProj K ι Q e Ψ hQ hΨ) hzero hdim hfin
  have hsm : ∀ j, ∀ J ∈ chartComponents (conePts Q) σ i, GroundTheory.Heights₂.Heights.SmoothNear
      (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (chartPot σ i N j) := fun j J hJ =>
    GroundTheory.Heights₂.Heights.smoothNear_chartPot σ i hN (fun x hx => by
      have hx' : x ∈ chartSet (conePts Q) σ i := by
        rw [← hzero]
        exact fun q hq => hx q ((mem_chartComponents.1 hJ).1.2 hq)
      obtain ⟨z, -, hzi, rfl⟩ := hx'
      simpa using hzi) j
  have hint : Integrable (fun y => ∑ J ∈ chartComponents (conePts Q) σ i,
      chartAbsDens J (chartProjMatrix σ Ψ) (chartWeight σ i G) (chartPot σ i N) y) :=
    integrable_finset_sum _ fun J hJ =>
      GlobalTheory.T.integrable_domCell_logNorm_chart K ι Q e _ σ i Ψ N A s a J hA hAa hs hGm hzero hJ (hfin J hJ) fun R C =>
        GlobalTheory.T.integrable_chartAbsDensity _ e J _ _ _ R C (mem_chartComponents.1 hJ).1.1 (hdim J hJ) (hfin J hJ)
          (GlobalTheory.T.chartSection_not_mem_components K ι Q e _ σ i s a hQ hs hsQ J hJ) fun j => hsm j J hJ
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
  filter_upwards [hfs] with y hy
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : cxPosDens (conePts Q) Ψ (pot N) G y =
      ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot N) G y w := by
    unfold cxPosDens
    exact finsum_congr fun w => finsum_congr fun _ => max_eq_left (hnn y w)
  rw [hpos, hy]
  exact Finset.sum_le_sum fun J _ =>
    GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.chartDens_le_chartAbsDens _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open GlobalTheory.CompanionTheory.Ar.Pub.CxChart in

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  intro K _ ι _ Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ
  classical
  obtain ⟨N, hN, hTw⟩ := GlobalTheory.T.exists_smooth_metrics_nonneg_density K ι e L hL
  obtain ⟨hnn, hbd⟩ := hTw (conePts Q) Ψ fun z hz => hz.1
  set G : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ := fun i => (domCell i).indicator (absLogNorm A s) with hG
  have hG0 : ∀ i z, 0 ≤ G i z := fun i z => Set.indicator_nonneg (fun z _ => by
    unfold absLogNorm
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl) z
  have hWm := fun i => GlobalTheory.T.domCell_logNorm_measurable_invariant K ι A s a i hA hAa hs
  have hcell : ∀ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) < ⊤ := by
    intro i
    by_cases hi : ∃ z ∈ conePts Q, segre z i ≠ 0
    · obtain ⟨Ψ', hΨ', hΨ0⟩ := GlobalTheory.T.exists_goodProj_first_coordinate K ι Q e i hQ hi
      rw [GlobalTheory.T.integral_density_independent_projection K ι Q e Ψ Ψ' N (G i) hQ hΨ hΨ' hN (hWm i).1 (hWm i).2]
      exact cell_mass_lt_top hQ hΨ' hΨ0 hN hA hAa hs hsQ fun y w => (hTw (conePts Q) Ψ' fun z hz => hz.1).1 _ y w (hG0 i)
    · have h0 : ∀ z ∈ conePts Q, G i z = 0 := fun z hz => Set.indicator_of_notMem (fun hzi =>
        hi ⟨z, hz, segre_ne_zero_of_mem_domCell hz.1 hzi⟩) _
      have : ∀ y, cxPosDens (conePts Q) Ψ (pot N) (G i) y = 0 := fun y => by
        unfold cxPosDens
        simp [setSheetDensity_eq_zero (pot N) h0]
      simp [this]
  have hfib := GlobalTheory.T.setFibre_finite_of_goodProj K ι Q e Ψ hQ hΨ
  have hcov : ∀ z ∈ conePts Q, |logNormC A s z| ≤ ∑ i, G i z := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_mem_domCell hz.1
    have : |logNormC A s z| = G i z := by
      simp only [hG, Set.indicator_of_mem hi, absLogNorm, if_pos hz.1]
    rw [this]
    exact Finset.single_le_sum (f := fun i => G i z) (fun i _ => hG0 i z) (Finset.mem_univ i)
  have hpt : ∀ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) ≤
      ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
    intro y
    have hnnd : ∀ i, 0 ≤ cxPosDens (conePts Q) Ψ (pot N) (G i) y := fun i =>
      finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnnd i, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold cxPosDens
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfib y)]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine (hbd _ (fun z => ∑ i, G i z) y w hcov).trans ?_
    rw [setSheetDensity_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => le_max_left _ _) (by positivity)
  calc ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|)
      ≤ ∫⁻ y, ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (3 ^ e) * ∑ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finset_sum' _ fun i _ =>
          (GlobalTheory.T.aemeasurable_cxPosDensity K ι Q e Ψ N (G i) hQ hΨ hN (hWm i).1 (hWm i).2).ennreal_ofReal]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.2 fun i _ => hcell i)
