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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

section Weight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_blockScale {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (fun p : Σ k, ι k => c p.1 * z p) s = (∏ k, c k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ q : (Σ k, ι k), (c q.1 * z q) ^ m q =
      (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), z q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [h1]; ring

theorem logNormC_blockScale (A : HermLine ι) {s : MRingOver ℂ ι} {a : K → ℕ}
    (hA : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : logNormC A s (fun p => c p.1 * z p) = logNormC A s z := by
  unfold logNormC
  rw [eval_blockScale hs c z]
  have hh : A.h (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ A.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hA k, zpow_natCast]
  rw [hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']

theorem segre_blockScale (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segre (fun p : Σ k, ι k => c p.1 * z p) i = (∏ k, c k) * segre z i := by
  simp only [segre, Finset.prod_mul_distrib]

theorem isClosed_domCell (i : (k : K) → ι k) : IsClosed (domCell i) := by
  have hc : ∀ j : (k : K) → ι k, Continuous fun z : (Σ k, ι k) → ℂ => ‖segre z j‖ := fun j => by
    have h : Continuous fun z : (Σ k, ι k) → ℂ => ∏ k, z ⟨k, j k⟩ :=
      continuous_finset_prod _ fun k _ => continuous_apply (⟨k, j k⟩ : Σ k, ι k)
    exact h.norm
  have : domCell i = ⋂ j, {z : (Σ k, ι k) → ℂ | ‖segre z j‖ ≤ ‖segre z i‖} := by
    ext z; simp [domCell]
  rw [this]
  exact isClosed_iInter fun j => isClosed_le (hc j) (hc i)

theorem blockScale_mem_domCell {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ)
    (i : (k : K) → ι k) : (fun p : Σ k, ι k => c p.1 * z p) ∈ domCell i ↔ z ∈ domCell i := by
  have hpos : 0 < ‖∏ k, c k‖ :=
    norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)
  simp only [domCell, Set.mem_setOf_eq, segre_blockScale, norm_mul]
  exact forall_congr' fun j =>
    ⟨fun h => le_of_mul_le_mul_left h hpos, fun h => mul_le_mul_of_nonneg_left h hpos.le⟩

theorem measurable_absLogNorm (A : HermLine ι) (hA : IsSmoothHerm A) (s : MRingOver ℂ ι) :
    Measurable (absLogNorm A s) := by
  classical
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hT
  have hTm : MeasurableSet T := isOpen_blockNonzero.measurableSet
  have hh : Measurable (T.piecewise A.h 1) :=
    hA.continuousOn.measurable_piecewise continuousOn_const hTm
  have heq : absLogNorm A s =
      T.piecewise (fun z => |Real.log (‖eval z s‖ / T.piecewise A.h 1 z)|) 0 := by
    funext z
    by_cases hz : z ∈ T
    · have hz' : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := hz
      rw [Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ hz]
      simp only [absLogNorm, if_pos hz', logNormC]
    · have hz' : ¬ ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := hz
      rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      simp only [absLogNorm, if_neg hz', Pi.zero_apply]
  rw [heq]
  refine Measurable.piecewise hTm ?_ measurable_const
  exact continuous_abs.measurable.comp
    (Real.measurable_log.comp ((MvPolynomial.continuous_eval s).norm.measurable.div hh))

theorem absLogNorm_blockScale (A : HermLine ι) {s : MRingOver ℂ ι} {a : K → ℕ}
    (hAa : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : absLogNorm A s (fun p => c p.1 * z p) = absLogNorm A s z := by
  have hmem : (∀ k, ∃ j, c k * z ⟨k, j⟩ ≠ 0) ↔ ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, hc, false_or]
  by_cases hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0
  · simp only [absLogNorm, if_pos hz, if_pos (hmem.2 hz), logNormC_blockScale A hAa hs hc z]
  · simp only [absLogNorm, if_neg hz, if_neg (mt hmem.1 hz)]

end Weight

theorem cutWeight_measurable_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by
  intro K _ ι _ A s a i hA hAa hs
  refine ⟨(measurable_absLogNorm A hA s).indicator (isClosed_domCell i).measurableSet, ?_⟩
  intro c z hc
  by_cases hz : z ∈ domCell i
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((blockScale_mem_domCell hc z i).2 hz),
      absLogNorm_blockScale A hAa hs hc z]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem (mt (blockScale_mem_domCell hc z i).1 hz)]

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
