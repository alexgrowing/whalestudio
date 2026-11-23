import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

def LogAbsLocIntStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ), IsOpen U → AnalyticOnNhd ℂ f U →
    LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume

theorem analyticAt_eval_poly {D : ℕ} {σ : Type*} (p : MvPolynomial σ ℂ)
    {γ : (Fin D → ℂ) → σ → ℂ} {u : Fin D → ℂ} (hγ : ∀ i, AnalyticAt ℂ (fun v => γ v i) u) :
    AnalyticAt ℂ (fun v => eval (γ v) p) u := by
  induction p using MvPolynomial.induction_on
  · simpa using analyticAt_const
  · rename_i p q hp hq
    have h := hp.add hq
    simp only [map_add]
    exact h
  · rename_i p i hp
    have h := hp.mul (hγ i)
    simp only [map_mul, MvPolynomial.eval_X]
    exact h

theorem abs_log_div_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by
  rcases ha.eq_or_lt with h | h
  · subst h
    simp
  · rw [Real.log_div h.ne' hb.ne', abs_le]
    constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
      le_abs_self (Real.log b), neg_abs_le (Real.log b)]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem brIntegrable_of (hLA : LogAbsLocIntStatement) (R : AnLogRes P J e)
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  classical
  obtain ⟨a, hAa, hsa, -⟩ := hs
  have hpot : ∀ i, IsPotential R.A (potOf R (L i)) := fun i => isPotential_potOf R (hL i)
  intro j Kc hKt hKc
  have hdens := locDensCont R.A (fun i => potOf R (L i)) hpot j
  have hloc : LocallyIntegrableOn
      (fun y => logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)))
      (R.A.chart j).target volume := by
    intro y0 hy0
    let x0 := (R.A.chart j).symm y0
    let V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0
    have hVo : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
    have hy0V : y0 ∈ V := ⟨hy0, R.mem_U x0⟩
    let γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun v => R.lift x0 ((R.A.chart j).symm v)
    let F : (Fin e → ℂ) → ℂ := fun v => eval (γ v) (map (Int.castRingHom ℂ) s)
    let H : (Fin e → ℂ) → ℝ := fun v => A.h (γ v)
    have hγa : ∀ y ∈ V, ∀ p, AnalyticAt ℂ (fun v => γ v p) y := fun y hy p => R.holo x0 p j y hy
    have hFan : AnalyticOnNhd ℂ F V := fun y hy => analyticAt_eval_poly _ (hγa y hy)
    have hγc : ContinuousOn γ V := continuousOn_pi.mpr (fun p => (R.holo x0 p j).continuousOn)
    have hnz : ∀ y ∈ V, ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := fun y hy => (R.mem x0 _ hy.2).1
    have hHpos : ∀ y ∈ V, 0 < H y := fun y hy => A.pos _ (hnz y hy)
    have hHc : ContinuousOn H V := hA.continuousOn.comp hγc (fun y hy => hnz y hy)
    have hlogH : ContinuousOn (fun y => Real.log (H y)) V := hHc.log (fun y hy => (hHpos y hy).ne')
    have hlogF : LocallyIntegrableOn (fun y => Real.log ‖F y‖) V volume := hLA e V F hVo hFan
    have hinv : ∀ y ∈ V, logNorm A s (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y)) =
        Real.log (‖F y‖ / H y) := by
      intro y hy
      obtain ⟨c, hc, hcz⟩ := R.compat ((R.A.chart j).symm y) x0 ((R.A.chart j).symm y)
        ⟨R.mem_U _, hy.2⟩
      rw [hcz]
      have h1 := logNorm_bsmul A hAa hsa hc (R.lift x0 ((R.A.chart j).symm y))
      exact h1
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVo y0 hy0V
    have hBV : Metric.closedBall y0 (δ / 2) ⊆ V :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hBc : IsCompact (Metric.closedBall y0 (δ / 2)) := isCompact_closedBall y0 (δ / 2)
    have hBm : MeasurableSet (Metric.closedBall y0 (δ / 2)) :=
      Metric.isClosed_closedBall.measurableSet
    refine ⟨Metric.closedBall y0 (δ / 2),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩
    have hmeas : AEStronglyMeasurable (fun y => Real.log (‖F y‖ / H y))
        (volume.restrict (Metric.closedBall y0 (δ / 2))) := by
      have hF' : AEMeasurable (fun y => ‖F y‖) (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        ((hFan.continuousOn.mono hBV).aestronglyMeasurable hBm).norm.aemeasurable
      have hH' : AEMeasurable H (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        ((hHc.mono hBV).aestronglyMeasurable hBm).aemeasurable
      exact (Real.measurable_log.comp_aemeasurable (hF'.div hH')).aestronglyMeasurable
    have hint : IntegrableOn (fun y => Real.log (‖F y‖ / H y)) (Metric.closedBall y0 (δ / 2))
        volume := by
      have hb : Integrable (fun y => |Real.log ‖F y‖| + |Real.log (H y)|)
          (volume.restrict (Metric.closedBall y0 (δ / 2))) :=
        (Integrable.abs (hlogF.integrableOn_compact_subset hBV hBc)).add
          (Integrable.abs ((hlogH.mono hBV).integrableOn_compact hBc))
      refine hb.mono' hmeas ?_
      refine (ae_restrict_iff' hBm).mpr (Filter.Eventually.of_forall (fun y hy => ?_))
      rw [Real.norm_eq_abs]
      exact abs_log_div_le (norm_nonneg _) (hHpos y (hBV hy))
    exact hint.congr_fun (fun y hy => (hinv y (hBV hy)).symm) hBm
  exact (hloc.integrableOn_compact_subset hKt hKc).mul_continuousOn (hdens.mono hKt) hKc

end ReciprocityTheory.ChartRestriction.G.Geo
