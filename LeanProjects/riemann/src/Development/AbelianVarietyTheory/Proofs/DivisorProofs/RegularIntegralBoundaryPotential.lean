import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointDimensionLtProjectiveLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetInterPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOnNhdOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPshExhaustionWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSumIntegralLeMongeAmpere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableAbsLogNormSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereExhaustionLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySectionPullbackBound
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open ReciprocityTheory.AnForm.P GlobalTheory.Mean4O GlobalTheory.LogResCurv
open scoped ENNReal

namespace GlobalTheory.LogRInt

theorem uniform_bound (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ)
    (hS : IsBoundarySetting A α Λ σ c)
    (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y)
    (hB : IsProjective B) (μ : Y → X) (hμ : HoloMap B A μ)
    (hint : ∀ i, interior {y | σ i (μ y) (μ y) = 0} = ∅)
    (w : ℕ → X → ℝ) (K : ℝ) (hw : ∀ R, A.Smooth (w R)) (hwp : ∀ R, IsPsh A (α + LocPot.ofFun (w R)))
    (hwb : ∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) :
    ∃ C : ℝ, ∀ R, MIntegrable B (fun _ => (α + LocPot.ofFun (w R)).pullback μ hμ.1)
        (GlobalTheory.Mean4O.cut (μ ⁻¹' boundary σ) Set.univ
          fun y => Real.log (Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (μ y))) ∧
      mInt B (fun _ => (α + LocPot.ofFun (w R)).pullback μ hμ.1)
        (GlobalTheory.Mean4O.cut (μ ⁻¹' boundary σ) Set.univ
          fun y => Real.log (Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (μ y))) ≤ C := by
  obtain ⟨hα, hαp, hσ, -⟩ := hS
  obtain ⟨Om, hO, hOpos⟩ := GlobalTheory.FubiniStudyPot.exists_posPot n Y B hB
  have hOp := TailBoundAlt.isPsh_of_isPosPot B Om hOpos
  have hBd := GlobalTheory.isBd_pullback_boundary d X A m Λ σ (fun i => ⟨(hσ i).1, (hσ i).2.1, (hσ i).2.2.2⟩) n Y B μ hμ hint
    Om hO hOpos
  set Z := μ ⁻¹' boundary σ with hZ
  set ρ : Y → ℝ := fun y => Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (μ y) with hρ
  have hα' := isPotentialPullback A B μ hμ α hα
  obtain ⟨K₂, hK₂, ha1, ha2⟩ := TailBoundAlt.exists_psh_chern_bound B Om _ hO hOpos hα'
  have hKm : 0 ≤ max K 0 * (1 + (m : ℝ)) := by positivity
  set K' := K₂ + max K 0 * (1 + (m : ℝ)) with hK'
  have hρe := hBd.2.2.2.2.2.1
  obtain ⟨C, hC⟩ := GlobalTheory.Mean4O.LogTail.tail n Y B Z ρ Om hBd K'
  have ha1' := psh_mono B hO hOp hα' ha1 (C' := K') (by linarith)
  have ha2' := psh_mono B hO hOp (isPotentialRsmul B _ _ hα') ha2 (C' := K') (by linarith)
  refine ⟨C * Real.log (Real.exp 1) ^ (n + 1) / Real.exp 1, fun R => ?_⟩
  have hg := smooth_comp_holo A B μ hμ _ (hw R)
  have hgb : ∀ y, y ∉ Z → -(K' * Real.log (ρ y)) ≤ w R (μ y) ∧ w R (μ y) ≤ 0 := fun y hy => by
    obtain ⟨h1, h2⟩ := hwb R (μ y) hy
    refine ⟨le_trans ?_ h1, h2⟩
    obtain ⟨h3, h4⟩ := sum_log_le (fun i => logNormSec (Λ i) (σ i) (μ y))
      fun i => logNormSec_nonpos ((hσ i).2.2.2 _)
    have h5 : 0 ≤ Real.log (ρ y) := Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (hρe y hy))
    have h6 := mul_le_mul (le_max_left K 0) h4 h3 (le_max_right K 0)
    have h7 := mul_nonneg hK₂ h5
    have h8 : K' * Real.log (ρ y) =
        K₂ * Real.log (ρ y) + max K 0 * ((1 + (m : ℝ)) * Real.log (ρ y)) := by rw [hK']; ring
    rw [h8]
    exact neg_le_neg (h6.trans (le_add_of_nonneg_left h7))
  have hwR := isPotentialAdd A _ _ hα (isPotential_ofFun A _ (hw R))
  have hl : ListForm B Z ρ Om K' ((α + LocPot.ofFun (w R)).pullback μ hμ.1) := by
    have hp := GlobalTheory.PshPull.isPsh_pullback d X A n Y B μ hμ _ hwR (hwp R)
    rw [pullback_add_ofFun] at hp ⊢
    exact listForm_add B hα' ha1' ha2' hg hgb hp
  obtain ⟨hI, -, htail⟩ := hC (fun _ => (α + LocPot.ofFun (w R)).pullback μ hμ.1) fun _ => hl
  have h1 := htail (Real.exp 1) le_rfl
  have hcut : (GlobalTheory.Mean4O.cut Z {x | Real.exp 1 ≤ ρ x} fun x => Real.log (ρ x)) =
      GlobalTheory.Mean4O.cut Z Set.univ fun x => Real.log (ρ x) := by
    unfold GlobalTheory.Mean4O.cut
    congr 1
    ext x
    exact ⟨fun h => ⟨trivial, h.2⟩, fun h => ⟨hρe x h.2, h.2⟩⟩
  rw [hcut] at h1
  exact ⟨hI, h1⟩

theorem onResolution (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ)
    (hS : IsBoundarySetting A α Λ σ c)
    (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y)
    (hB : IsProjective B) (μ : Y → X) (hμ : HoloMap B A μ)
    (hint : ∀ i, interior {y | σ i (μ y) (μ y) = 0} = ∅) :
    chartSumInt B ((poincarePot α Λ σ c).pullback μ hμ.1) (μ ⁻¹' boundary σ)ᶜ
      (fun y => ENNReal.ofReal (1 + ∑ i, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.rFun (Λ i) (σ i) (μ y)))) < ∞ := by
  obtain ⟨w, K, O, hw, hpsh, hbd, hO, hmono, -, hcov, hloc⟩ :=
    GlobalTheory.PoincareTrunc.smoothTrunc d X A m α Λ σ c hS
  obtain ⟨C, hC⟩ := uniform_bound d X A m α Λ σ c hS n Y B hB μ hμ hint w K hw hpsh hbd
  have hσ := hS.2.2.1
  set g : Y → ℝ := GlobalTheory.Mean4O.cut (μ ⁻¹' boundary σ) Set.univ
    fun y => Real.log (Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (μ y)) with hg
  have hcn : ∀ i, Continuous fun y => normSec (Λ i) (σ i) (μ y) := fun i =>
    (GlobalTheory.AbsLogNormMeas.continuous_normSec A (Λ i) (σ i) (hσ i).1 (hσ i).2.1).comp hμ.1
  have hZc : IsClosed (μ ⁻¹' boundary σ) := by
    have : μ ⁻¹' boundary σ = ⋃ i, (fun y => normSec (Λ i) (σ i) (μ y)) ⁻¹' {0} := by
      ext y
      simp [boundary, normSec]
    rw [this]
    exact isClosed_iUnion_of_finite fun i => isClosed_singleton.preimage (hcn i)
  have hgm : ∀ [MeasurableSpace Y] [BorelSpace Y], Measurable g := by
    intro _ _
    refine Measurable.indicator ?_ (MeasurableSet.univ.inter hZc.measurableSet.compl)
    exact (measurable_const.sub (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => (hcn i).measurable.log))).log
  have hsl := fun y => sum_log_le (fun i => logNormSec (Λ i) (σ i) (μ y))
      fun i => logNormSec_nonpos ((hσ i).2.2.2 _)
  have hm1 : (0 : ℝ) < 1 + m := by positivity
  have hg0 : ∀ y, 0 ≤ g y := fun y => Set.indicator_nonneg
    (fun y _ => nonneg_of_mul_nonneg_right ((hsl y).1.trans (hsl y).2) hm1) y
  have hpotX : ∀ R, IsPotential A (α + LocPot.ofFun (w R)) := fun R =>
    isPotentialAdd A _ _ hS.1 (isPotential_ofFun A _ (hw R))
  letI : MeasurableSpace Y := borel Y
  haveI : BorelSpace Y := ⟨rfl⟩
  have hfin : chartSumInt B ((poincarePot α Λ σ c).pullback μ hμ.1) (μ ⁻¹' boundary σ)ᶜ
      (fun y => ENNReal.ofReal (1 + m) * ENNReal.ofReal (g y)) < ∞ := by
    refine GlobalTheory.chartSumInt_lt_top_of_monotone_limit d X A n Y B μ hμ (poincarePot α Λ σ c)
      (fun R => α + LocPot.ofFun (w R)) O (fun _ => 0) _ _
      ((B.n : ℝ≥0∞) * (ENNReal.ofReal (1 + m) * ENNReal.ofReal C)) hpotX hO hmono ?_ ?_ ?_ ?_ ?_
    · intro R x y hy
      show α.φ x y + w R y = α.φ x y + pFun Λ σ c y / 2 + 0
      rw [hloc R y hy, add_zero]
    · intro y hy
      exact hcov (μ y) hy
    · intro _ _
      exact measurable_const.mul hgm.ennreal_ofReal
    · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    · intro R
      have hp := isPotentialPullback A B μ hμ _ (hpotX R)
      have hq := GlobalTheory.PshPull.isPsh_pullback d X A n Y B μ hμ _ (hpotX R) (hpsh R)
      refine (GlobalTheory.ChartSumBound.chartSumInt_le_card_mul n Y B _ hp hq _ _
        (measurable_const.mul hgm.ennreal_ofReal)).trans ?_
      simp only [Pi.mul_apply]
      rw [lintegral_const_mul _ hgm.ennreal_ofReal]
      obtain ⟨-, hthm⟩ := maMeasure_thm B (fun _ => (α + LocPot.ofFun (w R)).pullback μ hμ.1)
        (fun _ => hp) (fun _ => hq)
      obtain ⟨hiff, heq⟩ := hthm g hgm
      rw [← ofReal_integral_eq_lintegral_ofReal (hiff.1 (hC R).1) (Filter.Eventually.of_forall hg0),
        ← heq (hC R).1]
      gcongr
      exact (hC R).2
  refine lt_of_le_of_lt ?_ hfin
  refine Finset.sum_le_sum fun j _ => ?_
  refine setLIntegral_mono' ((B.chart j).isOpen_inter_preimage_symm hZc.isOpen_compl).measurableSet
    fun z hz => ?_
  refine mul_le_mul_left ?_ _
  beta_reduce
  rw [← ENNReal.ofReal_mul hm1.le, hg, GlobalTheory.Mean4O.cut,
    Set.indicator_of_mem (show (B.chart j).symm z ∈ Set.univ ∩ (μ ⁻¹' boundary σ)ᶜ from ⟨trivial, hz.2⟩)]
  exact ENNReal.ofReal_le_ofReal (hsl _).2

theorem logR_integrable_of_resolution (hR : GlobalTheory.Published.AnalyticLogResolution)
    (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X)
    (hproj : IsProjective A) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ)
    (hset : IsBoundarySetting A α Λ σ c) (Z : Set X) (n : ℕ) (hZ : IsIrreducibleAnalytic A Z)
    (hreg : (regularLocus A Z n).Nonempty) (hZbd : ¬ Z ⊆ boundary σ) :
    regIntegral A Z n (poincarePot α Λ σ c) (regularLocus A Z n \ boundary σ)
      (fun y => ENNReal.ofReal (1 + ∑ i, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.rFun (Λ i) (σ i) y))) < ⊤ := by
  have ht : ∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧ ∃ y ∈ Z, σ i y y ≠ 0 := by
    intro i
    obtain ⟨y, hyZ, hybd⟩ := Set.not_subset.1 hZbd
    exact ⟨(hset.2.2.1 i).1, (hset.2.2.1 i).2.1, y, hyZ, fun h => hybd ⟨i, h⟩⟩
  obtain ⟨Y, tY, cY, t2Y, B, μ, hμ, S, r, W, e, J, hBproj, hrange, hS, -, hdense, hinj, himm, hSW, hsnc⟩ :=
    hR d X A hproj Z n hZ hreg m _ _ ht
  have hhyp : ∀ y, ∃ χ : OpenPartialHomeomorph Y (Fin n → ℂ), IsCompatChart B χ ∧ y ∈ χ.source ∧
      ∃ J' : Finset (Fin n), μ ⁻¹' S ∩ χ.source = {w ∈ χ.source | ∃ a ∈ J', χ w a = 0} := by
    intro y
    obtain ⟨χ, hχ, hy, κ, -, hW, -⟩ := hsnc y
    classical
    refine ⟨χ, hχ, hy, Finset.univ.filter (fun a => ∃ k ∈ J, κ k = some a), ?_⟩
    ext w
    simp only [hSW, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨⟨k, hk, hwk⟩, hw⟩
      have := (hW k).le ⟨hwk, hw⟩
      obtain ⟨a, ha, hwa⟩ := this.2
      exact ⟨hw, a, ⟨k, hk, ha⟩, hwa⟩
    · rintro ⟨hw, a, ⟨k, hk, ha⟩, hwa⟩
      have : w ∈ W k ∩ χ.source := (hW k).ge ⟨hw, a, ha, hwa⟩
      exact ⟨⟨k, hk, this.1⟩, hw⟩
  have hint : ∀ i, interior {y | σ i (μ y) (μ y) = 0} = ∅ := fun i => by
    have hsec := GlobalTheory.isSection_pullback_holoMap d n X Y A B μ hμ (Λ i) (σ i) (ht i).2.1
    refine LeviFormBoundaryTopology.interior_bdry_eq_empty (m := e i) (W := W) hsec fun y => ?_
    obtain ⟨χ, h1, h2, κ, h3, h4, h5⟩ := hsnc y
    obtain ⟨h6, u, h7, h8, h9⟩ := h5 i
    exact ⟨χ, h1, h2, h6, κ, h3, h4, u, h7, h8, h9⟩
  exact lt_of_le_of_lt (GlobalTheory.RegToResolution.regIntegral_le_chartSumInt d X A Z n Y B μ hμ S (boundary σ) hrange hS
    hdense hinj himm hhyp (poincarePot α Λ σ c)
    (GlobalTheory.PoincSmooth.smoothOn_nhd_off_boundary d X A m α Λ σ c hset.1
      (fun i => ⟨(hset.2.2.1 i).1, (hset.2.2.1 i).2.1⟩) (fun i => (hset.2.2.1 i).2.2.2)) _)
    (onResolution d X A m α Λ σ c hset n Y B hBproj μ hμ hint)

theorem logR_integrable : GlobalTheory.Published.AnalyticLogResolution → GlobalTheory.Published.AnalyticSetDimension →
    ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    IsProjective A → ∀ (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (sg : Fin m → X → X → ℂ) (t : ℝ),
    IsBoundarySetting A α Λ sg t → ∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z →
    (regularLocus A Z n).Nonempty → ¬ Z ⊆ boundary sg →
    regIntegral A Z n (poincarePot α Λ sg t) (regularLocus A Z n \ boundary sg)
      (fun y => ENNReal.ofReal (1 + ∑ i, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.rFun (Λ i) (sg i) y))) < ⊤ :=
  fun hR _ d X _ _ _ A hA m α Λ sg t hS Z n hZ hreg hb =>
    logR_integrable_of_resolution hR d X A hA m α Λ sg t hS Z n hZ hreg hb

end GlobalTheory.LogRInt
