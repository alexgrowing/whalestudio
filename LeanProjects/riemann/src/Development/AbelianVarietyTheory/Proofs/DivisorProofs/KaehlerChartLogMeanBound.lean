import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBd
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallFiniteChartCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JensenLogMeanCutoffStatement

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

namespace GlobalTheory.LogMean

variable {k : Type} [CommRing k] {Y : AlgebraicGeometry.Scheme.{0}} {p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {σ : k →+* ℂ}
  {d : ℕ}

theorem integrable_rhoIn_chart {R : GlobalTheory.AnRead p σ d} {a : GlobalTheory.ShFam.ChartForm p σ d} {E : GlobalTheory.ChernReg.ChartMap p σ d}
    (ha : GlobalTheory.ShFam.IsKaehlerForm R a) (hE : GlobalTheory.ChernReg.IsExph a E) (ψ : GlobalTheory.CxPts p σ → ℝ)
    {c c' : GlobalTheory.AlgChart p σ d} {y : GlobalTheory.CxPts p σ} (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) (t : ℝ)
    (h : Integrable (fun ξ => ψ (E c' y (t • ξ)) * GlobalTheory.ChernReg.cutoff (a c' y ξ))) :
    Integrable (fun ξ => ψ (E c y (t • ξ)) * GlobalTheory.ChernReg.cutoff (a c y ξ)) := by
  let L : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := (WithLp.linearEquiv 2 ℂ _).toLinearMap ∘ₗ
    (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y)).toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap
  have hL : Function.Injective (L.restrictScalars ℝ) := (injective_iff_map_eq_zero _).2 fun ξ h =>
    by_contra fun h0 => GlobalTheory.AlgChart.dtrans_ne_zero hy hy' h0 h
  let T := LinearEquiv.ofInjectiveEndo _ hL
  have e : (fun ξ => ψ (E c y (t • ξ)) * GlobalTheory.ChernReg.cutoff (a c y ξ)) =
      (fun ξ => ψ (E c' y (t • ξ)) * GlobalTheory.ChernReg.cutoff (a c' y ξ)) ∘ T :=
    funext fun ξ => congrArg₂ (· * ·)
      (congrArg ψ ((hE.trans c c' y hy hy' _).trans (congrArg _ (map_smul T t ξ))))
      (congrArg GlobalTheory.ChernReg.cutoff (ha.trans hy hy' ξ))
  have hT := T.isUnit_det'.ne_zero
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin d → ℂ)) hT
  have h2 : Integrable (fun ξ => ψ (E c' y (t • ξ)) * GlobalTheory.ChernReg.cutoff (a c' y ξ))
      (Measure.map (T.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv) volume) := by
    have : (Measure.map (T.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv) volume) =
        Measure.map (⇑(T : (Fin d → ℂ) →ₗ[ℝ] (Fin d → ℂ))) volume := rfl
    rw [this, hm]
    exact h.smul_measure ENNReal.ofReal_ne_top
  rw [e]
  exact (integrable_map_equiv T.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv _).1 h2

theorem rhoIn_log_le_log_log : GlobalTheory.HeightParts.KernelSt → ∀ {k : Type} [CommRing k] {Y : AlgebraicGeometry.Scheme.{0}}
    {p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {σ : k →+* ℂ} {d : ℕ} [SmoothOfRelativeDimension d p]
    [CompactSpace (GlobalTheory.CxPts p σ)] (a : GlobalTheory.ShFam.ChartForm p σ d) (E : GlobalTheory.ChernReg.ChartMap p σ d)
    (f : GlobalTheory.CxPts p σ → ℝ), GlobalTheory.ShFam.IsKaehlerForm (GlobalTheory.AnRead.all p σ d) a → GlobalTheory.ChernReg.IsExph a E →
    (∀ y, Real.exp 1 ≤ f y) → (∀ y₀, ∃ ch : GlobalTheory.AlgChart p σ d, y₀ ∈ ch.e.source ∧
      GlobalTheory.LogMean.LogBallBd (f ∘ ch.e.symm) (ch.e y₀) (2 * d)) →
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (ch : GlobalTheory.AlgChart p σ d) (y : GlobalTheory.CxPts p σ),
      y ∈ ch.e.source → MeasureTheory.Integrable (fun ξ => Real.log (f (E ch y (t • ξ))) *
        GlobalTheory.ChernReg.cutoff (a ch y ξ)) ∧
      GlobalTheory.ChernReg.rhoIn a E (fun z => Real.log (f z)) ch y t ≤ Real.log (C * Real.log (1 / t)) := by
  intro hK k _ Y p σ d _ _ a E f ha hE hf hloc
  obtain ⟨n, ch, K, C0, ρ0, hC0, hρ0, hKc, hcov, hball⟩ := GlobalTheory.T.log_ball_finite_chart_cover f hloc
  have hKj := fun j => hK k Y p σ d a E ha hE (ch j) (K j) (hKc j).1 (hKc j).2
  choose Cj tj hCj htj hj using hKj
  have hfpos : ∀ z, 0 < f z := fun z => (Real.exp_pos 1).trans_le (hf z)
  have hf1 : ∀ z, 1 ≤ f z := fun z => by linarith [Real.add_one_le_exp 1, hf z]
  have hterm : ∀ i, 0 ≤ 1 / tj i + Cj i / ρ0 := fun i => by have := hCj i; have := htj i; positivity
  set S := ∑ i, (1 / tj i + Cj i / ρ0) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hterm i
  set A : Fin n → ℝ := fun i => Cj i ^ (2 * d + 1) * C0 * (2 + |Real.log (1 / Cj i)|) with hA
  have hA0 : ∀ i, 0 ≤ A i := fun i => by have := hCj i; positivity
  have hsA : 0 ≤ ∑ i, A i := Finset.sum_nonneg fun i _ => hA0 i
  refine ⟨1 + ∑ i, A i, 1 / (3 + S), by linarith, by positivity, ?_⟩
  intro t ht htt c y hy
  obtain ⟨j, hyj, hKy⟩ := hcov y
  have hinv : 3 + S ≤ 1 / t := by
    rw [le_div_iff₀ ht]
    rw [le_div_iff₀ (by positivity)] at htt
    linarith
  have hsj : 1 / tj j + Cj j / ρ0 ≤ S :=
    Finset.single_le_sum (f := fun i => 1 / tj i + Cj i / ρ0) (fun i _ => hterm i) (Finset.mem_univ j)
  have hCj0 := hCj j
  have htj0 := htj j
  have hq1 : 0 ≤ Cj j / ρ0 := by positivity
  have hq2 : 0 ≤ 1 / tj j := by positivity
  have htj' : t ≤ tj j := (one_div_le_one_div htj0 ht).1 (by linarith)
  have hCt : Cj j * t ≤ ρ0 := by
    have h1 : Cj j / ρ0 ≤ 1 / t := by linarith
    rw [div_le_div_iff₀ hρ0 ht] at h1
    linarith
  have hL1 : 1 ≤ Real.log (1 / t) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 1 / t by linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at h
  obtain ⟨-, -, hint⟩ := hj j y hyj hKy t ht htj'
  obtain ⟨hIf, hIbd⟩ := hball j _ hKy (Cj j * t) (mul_pos hCj0 ht) hCt
  have hIlog : IntegrableOn ((fun z => Real.log (f z)) ∘ (ch j).e.symm)
      (Metric.ball ((ch j).e y) (Cj j * t)) := by
    refine Integrable.mono' hIf (Real.measurable_log.comp_aemeasurable hIf.aemeasurable).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (Real.log_nonneg (hf1 _))]
    linarith [Real.log_le_sub_one_of_pos (hfpos ((ch j).e.symm v))]
  obtain ⟨hIgf, hbdf⟩ := hint f hIf
  obtain ⟨hIgl, -⟩ := hint (fun z => Real.log (f z)) hIlog
  refine ⟨integrable_rhoIn_chart ha hE (fun z => Real.log (f z)) hy hyj t hIgl, ?_⟩
  obtain ⟨hqc, hqh⟩ := GlobalTheory.ChernReg.continuous_and_smul ha hyj
  have hqp := ha.2 (ch j) y hyj
  have hJ := GlobalTheory.T.jensen_log_mean_cutoff (a (ch j) y) (fun ξ => f (E (ch j) y (t • ξ))) hqc hqh hqp (fun ξ => hf1 _) hIgf hIgl
  have hrho : GlobalTheory.ChernReg.rho a E f y t = GlobalTheory.ChernReg.mean (a (ch j) y) (fun ξ => f (E (ch j) y (t • ξ))) :=
    GlobalTheory.ChernReg.rho_eq ha hE f hyj t
  have hmean : Real.exp 1 ≤ GlobalTheory.ChernReg.mean (a (ch j) y) (fun ξ => f (E (ch j) y (t • ξ))) := by
    have hm := GlobalTheory.ChernReg.mass_pos hqc hqh hqp
    rw [GlobalTheory.ChernReg.mean, le_div_iff₀ hm, ← integral_const_mul]
    exact integral_mono ((GlobalTheory.ChernReg.integrable_cutoff hqc hqh hqp).const_mul _) hIgf
      fun ξ => mul_le_mul_of_nonneg_right (hf _) (GlobalTheory.ChernReg.cutoff_nonneg _)
  have habs : ∫ v in Metric.ball ((ch j).e y) (Cj j * t), |f ((ch j).e.symm v)| =
      ∫ v in Metric.ball ((ch j).e y) (Cj j * t), f ((ch j).e.symm v) := by
    congr 1
    funext v
    exact abs_of_pos (hfpos _)
  have hsplit : Real.log (1 / (Cj j * t)) = Real.log (1 / Cj j) + Real.log (1 / t) := by
    rw [← one_div_mul_one_div, Real.log_mul (by positivity) (by positivity)]
  have key : ∀ X : ℝ, Cj j / t ^ (2 * d) * (C0 * (Cj j * t) ^ (2 * d) * X) = Cj j ^ (2 * d + 1) * C0 * X := by
    intro X
    rw [mul_pow]
    field_simp
    ring
  have h1 : GlobalTheory.ChernReg.rho a E f y t ≤
      Cj j ^ (2 * d + 1) * C0 * (1 + Real.log (1 / Cj j) + Real.log (1 / t)) := by
    calc GlobalTheory.ChernReg.rho a E f y t ≤ |GlobalTheory.ChernReg.rho a E f y t| := le_abs_self _
      _ ≤ Cj j / t ^ (2 * d) * ∫ v in Metric.ball ((ch j).e y) (Cj j * t), |f ((ch j).e.symm v)| := hbdf
      _ = Cj j / t ^ (2 * d) * ∫ v in Metric.ball ((ch j).e y) (Cj j * t), f ((ch j).e.symm v) := by rw [habs]
      _ ≤ Cj j / t ^ (2 * d) * (C0 * (Cj j * t) ^ (2 * d) * (1 + Real.log (1 / (Cj j * t)))) :=
          mul_le_mul_of_nonneg_left hIbd (by positivity)
      _ = _ := by rw [key, hsplit]; ring
  have h2 : Cj j ^ (2 * d + 1) * C0 * (1 + Real.log (1 / Cj j) + Real.log (1 / t)) ≤ A j * Real.log (1 / t) := by
    have hl := le_abs_self (Real.log (1 / Cj j))
    have hp := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + |Real.log (1 / Cj j)|) (sub_nonneg.2 hL1)
    have hin : 1 + Real.log (1 / Cj j) + Real.log (1 / t) ≤
        (2 + |Real.log (1 / Cj j)|) * Real.log (1 / t) := by nlinarith
    calc _ ≤ Cj j ^ (2 * d + 1) * C0 * ((2 + |Real.log (1 / Cj j)|) * Real.log (1 / t)) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = A j * Real.log (1 / t) := by rw [hA]; ring
  have h3 : A j * Real.log (1 / t) ≤ (1 + ∑ i, A i) * Real.log (1 / t) := by
    have := Finset.single_le_sum (fun i _ => hA0 i) (Finset.mem_univ j)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  calc GlobalTheory.ChernReg.rhoIn a E (fun z => Real.log (f z)) c y t
        = GlobalTheory.ChernReg.rhoIn a E (fun z => Real.log (f z)) (ch j) y t := GlobalTheory.ChernReg.rhoIn_eq ha hE _ hy hyj t
    _ ≤ Real.log (GlobalTheory.ChernReg.mean (a (ch j) y) (fun ξ => f (E (ch j) y (t • ξ)))) := hJ
    _ ≤ Real.log ((1 + ∑ i, A i) * Real.log (1 / t)) :=
        Real.log_le_log (by linarith [Real.exp_pos 1]) (hrho ▸ (h1.trans (h2.trans h3)))

end GlobalTheory.LogMean
