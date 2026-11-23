import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreFinite
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_div_jacN (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) (hxS : x ∉ S) :
    locDens A Φ j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) = pushDens A Φ q x := by
  set c := chartIdx A x
  have hc : x ∈ (A.chart c).source := Classical.choose_spec (A.cover x)
  set u := A.chart j x
  have hsu : (A.chart j).symm u = x := (A.chart j).left_inv hx
  set T := A.chart c ∘ (A.chart j).symm with hTdef
  have hT : AnalyticAt ℂ T u :=
    A.holo j c u ⟨(A.chart j).map_source hx, by rw [Set.mem_preimage, hsu]; exact hc⟩
  have hTu : T u = A.chart c x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQc := (hq x hxS c hc).1
  have hQj := (hq x hxS j hx).2
  have heq : q ∘ (A.chart j).symm =ᶠ[𝓝 u] (q ∘ (A.chart c).symm) ∘ T := by
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm (A.chart c).open_source).mem_nhds
      (⟨(A.chart j).map_source hx, by rw [Set.mem_preimage, hsu]; exact hc⟩ :
        u ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart c).source)] with v hv
    simp only [hTdef, Function.comp_apply, (A.chart c).left_inv hv.2]
  have hder : fderiv ℂ (q ∘ (A.chart j).symm) u =
      (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x)).comp (fderiv ℂ T u) := by
    rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQc.differentiableAt) hT.differentiableAt,
      hTu]
  have hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
    rw [hder]
    exact LinearMap.det_comp _ _
  have hloc : locDens A Φ j u = locDens A Φ c (A.chart c x) *
      ‖LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
    have := GlobalTheory.CompanionTheory.Ar.Giv.MeasOff.locDens_chart_of_contDiffAt A Φ j c
      ((A.chart j).map_source hx) (by rw [hsu]; exact hc)
      (fun i => by rw [hsu]; exact hsm x hxS i c hc)
    rw [hsu, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq] at this
    exact this
  have hne := hQj
  rw [hdet] at hne
  have hc1 : ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr (left_ne_zero_of_mul hne)
  have hc2 : ‖LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (right_ne_zero_of_mul hne)
  unfold jacN pushDens
  rw [hloc, hdet, norm_mul, mul_pow, show chartIdx A x = c from rfl]
  field_simp

theorem sum_fibSum_ae (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (Pt : ChartPartition A)
    (h : Fin A.n → (Fin e → ℂ) → ℝ) (T : X → ℝ)
    (hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) = Pt.χ j x * T x) :
    ∀ᵐ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (h j) y = ∑ᶠ x ∈ q ⁻¹' {y} \ S, T x := by
  classical
  have hNall : ∀ᵐ y, ∀ j, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp (hN j)
  filter_upwards [hNall] with y hy
  have hterm' : ∀ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (h j) y =
      ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * T x := by
    intro j
    unfold fibSum
    rw [goodT_fibre_eq A q S hq j (hy j),
      finsum_mem_image ((A.chart j).injOn.mono Set.inter_subset_left)]
    refine (finsum_mem_congr (g := fun x => Pt.χ j x * T x) rfl
      fun x hx => hterm j x hx.1 hx.2.2).trans ?_
    refine finsum_mem_inter_support_eq' _ _ _ fun x hx => ?_
    have hχ : Pt.χ j x ≠ 0 := left_ne_zero_of_mul hx
    have hxs : x ∈ (A.chart j).source := Pt.tsupport_subset j (subset_tsupport _ hχ)
    exact ⟨fun h => h.2, fun h => ⟨hxs, h⟩⟩
  simp_rw [hterm']
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, Pt.sum_eq_one x, one_mul]

end GlobalTheory.CompanionTheory.Ar.Giv.Push
