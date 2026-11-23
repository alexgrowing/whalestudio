import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsMeasurable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterHironaka
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Set Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace PointsAbsMeasurable

section PushForward

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem integrable_absPushSum [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, |g x * pushDens A Φ q x|) := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set Pt := hne.some with hPt
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    |Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u| with hhj
  set Qj : Fin A.n → (Fin e → ℂ) → (Fin e → ℂ) := fun j => q ∘ (A.chart j).symm with hQj
  set N : Fin A.n → Set (Fin e → ℂ) :=
    fun j => Qj j '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) with hNdef
  have hN : ∀ j, volume (N j) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null (inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j)
  have hfib : ∀ j, ∀ y ∉ N j, goodT A q j ∩ Qj j ⁻¹' {y} =
      (A.chart j) '' ((A.chart j).source ∩ (q ⁻¹' {y} \ S)) :=
    fun j y hy => goodT_fibre_eq A q S hq j hy
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ Qj j ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [hfib j y hy]
    exact ((hfin y).subset inter_subset_right).image _
  have hint : ∀ j, Integrable (fibSum (goodT A q j) (Qj j) (hj j)) := fun j =>
    (area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((show IntegrableOn (hj j) (A.chart j).target volume from
        (integrableOn_chart A Pt Φ g hg j).abs).mono_set fun u hu => hu.1) (hfinj j)).1
  refine (integrable_finsetSum Finset.univ fun j _ => hint j).congr ?_
  have hNall : ∀ᵐ y, ∀ j, y ∉ N j :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp (hN j)
  filter_upwards [hNall] with y hy
  have hterm : ∀ j, fibSum (goodT A q j) (Qj j) (hj j) y =
      ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * |g x * pushDens A Φ q x| := by
    intro j
    unfold fibSum
    rw [hfib j y (hy j), finsum_mem_image ((A.chart j).injOn.mono inter_subset_left)]
    refine (finsum_mem_congr (g := fun x => Pt.χ j x * |g x * pushDens A Φ q x|) rfl
      fun x hx => ?_).trans ?_
    · have hJ : 0 ≤ jacN (Qj j) (A.chart j x) := by unfold jacN; positivity
      calc hj j (A.chart j x) / jacN (Qj j) (A.chart j x)
          = |Pt.χ j ((A.chart j).symm (A.chart j x)) * g ((A.chart j).symm (A.chart j x)) *
              locDens A Φ j (A.chart j x) / jacN (Qj j) (A.chart j x)| := by
            rw [abs_div, abs_of_nonneg hJ]
        _ = |Pt.χ j x * (g x * pushDens A Φ q x)| := by
            rw [fib_term A Φ hΦ q S hq Pt g j hx.1 hx.2.2]
        _ = Pt.χ j x * |g x * pushDens A Φ q x| := by
            rw [abs_mul, abs_of_nonneg (Pt.nonneg j x)]
    · refine finsum_mem_inter_support_eq' _ _ _ fun x hx => ?_
      have hχ : Pt.χ j x ≠ 0 := left_ne_zero_of_mul hx
      have hxs : x ∈ (A.chart j).source := Pt.tsupport_subset j (subset_tsupport _ hχ)
      exact ⟨fun h => h.2, fun h => ⟨hxs, h⟩⟩
  simp_rw [hterm]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, Pt.sum_eq_one x, one_mul]

end PushForward

section Res

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem absFibreSum_ae (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w| =
      ∑ᶠ x ∈ brQ R Ψ ⁻¹' {y} \ brBad R Ψ,
        |logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x| := by
  have hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)
  have hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) :=
    measure_eq_zero_iff_ae_notMem.mp hN
  filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y := fun h => hyN (Or.inl h)
  have hfib : fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, -, hx0, hxq, rfl⟩ := exists_of_mem_fibre R Ψ hw hy1
      exact ⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
      rwa [show brQ R Ψ x = y from hx.1] at this
  rw [hfib, finsum_mem_image ((brW_injOn R Ψ).mono fun x hx => show _ ∧ _ from
    ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩)]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_brW R Ψ L A s hP hL hs x hx.2
  rw [show brQ R Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dif_pos ⟨γ, hγ⟩]
  exact congrArg abs
    ((hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval)

end Res

end PointsAbsMeasurable

open PointsAbsMeasurable in

theorem PtsAbsMeasurable.proof (hE : ResExistsStatement) : PtsAbsMeasurable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  have hI := integrable_absPushSum R.A (fun j => potOf R (L j))
    (fun j => potOf_isPotential R (L j) (hL j)) (brQ R Ψ) (brBad R Ψ) (brBad_null R Ψ hP hΨ)
    (brGood R Ψ) (brFib_finite R Ψ hP hΨ) _ (brIntegrable R L A s hP hL hA hs)
  exact hI.aestronglyMeasurable.congr
    ((absFibreSum_ae R Ψ L A s hP hΨ hL hA hs).mono fun y hy => hy.symm)

end GroundTheory.Heights₂.Heights.Inter
