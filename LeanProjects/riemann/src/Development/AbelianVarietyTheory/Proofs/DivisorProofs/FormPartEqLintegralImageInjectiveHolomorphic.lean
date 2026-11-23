import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

open Function

namespace GlobalTheory.FlagCell2.ChangeOfVariables

theorem part_eq_lintegral_image : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (Ω : Set M) (Φ : M → V n) (γ : V n → Alt n), IsOpen Ω → Set.InjOn Φ Ω → (∀ x : A.Pt, x.pt ∈ Ω → DifferentiableAt ℂ (Φ ∘ x.ch.symm) x.crd ∧ β x = pull (fderiv ℂ (Φ ∘ x.ch.symm) x.crd) (γ (Φ x.pt))) → ∀ (s : ℤˣ) (T : Set M), MeasurableSet T → T ⊆ Ω → A.part β s T = ∫⁻ v in Φ '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
  intro M _ _ _ _ _ n A β hβ Ω Φ γ hΩ hinj hloc s T hT hTΩ
  set ρ : A.ι → M → ℝ≥0∞ := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring

  have chart : ∀ (i : A.ι) (P : Set M), MeasurableSet P → P ⊆ (A.e i).source → P ⊆ Ω →
      MeasurableSet (Φ '' P) ∧ A.part β s P =
        ∫⁻ v in Φ '' P, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
    intro i P hP hPs hPΩ
    set g : V n → V n := Φ ∘ (A.e i).symm with hg
    have hQ : MeasurableSet (A.e i '' P) := ChartGlue.measurableSet_image (A.e i) hP hPs
    have hder : ∀ v ∈ A.e i '' P, HasFDerivWithinAt g ((fderiv ℂ g v).restrictScalars ℝ) (A.e i '' P) v := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)).1.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjg : Set.InjOn g (A.e i '' P) := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
      simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy), (A.e i).left_inv (hPs hz)] at hyz
      rw [hinj (hPΩ hy) (hPΩ hz) hyz]
    have himg : Φ '' P = g '' (A.e i '' P) := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    refine ⟨himg ▸ measurable_image_of_fderivWithin hQ hder hinjg, ?_⟩
    rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hP hPs, ChartGlue.chartMeas_apply_of_subset _ _ hP hPs, himg,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hQ hder hinjg]
    refine setLIntegral_congr_fun hQ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hx := hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)
    have hl := A.loc_crd β (⟨(i, y), hPs hy⟩ : A.Pt)
    have hdet : ((fderiv ℂ g (A.e i y)).restrictScalars ℝ).det = Algebra.norm ℝ (fderiv ℂ g (A.e i y)).det :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ g (A.e i y) : V n →ₗ[ℂ] V n))
    have hx2 : β ⟨(i, y), hPs hy⟩ = pull (fderiv ℂ g (A.e i y)) (γ (Φ y)) := hx.2
    have hgy : g (A.e i y) = Φ y := by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    beta_reduce
    rw [hdet, hgy]
    simp only [hρ, (A.e i).left_inv (hPs hy)]
    erw [hl, hx2, dens_pull]
    rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
      Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

  rcases Set.eq_empty_or_nonempty T with rfl | ⟨y₀, -⟩
  · simp
  obtain ⟨C, hCc, hCU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun j => (A.e j).source)
    (fun j => (A.e j).open_source)
  obtain ⟨f, hf⟩ := (hCc.insert (A.cover y₀).choose).exists_eq_range (Set.insert_nonempty _ _)
  set U : ℕ → Set M := fun k => (A.e (f k)).source with hU
  have hUo : ∀ k, IsOpen (U k) := fun k => (A.e (f k)).open_source
  set P : ℕ → Set M := fun k => T ∩ disjointed U k with hPdef
  have hPm : ∀ k, MeasurableSet (P k) := fun k =>
    hT.inter (MeasurableSet.disjointed (fun k => (hUo k).measurableSet) k)
  have hPU : ∀ k, P k ⊆ U k := fun k => Set.inter_subset_right.trans (disjointed_subset U k)
  have hPΩ : ∀ k, P k ⊆ Ω := fun k => Set.inter_subset_left.trans hTΩ
  have hPd : Pairwise (Disjoint on P) := (disjoint_disjointed U).mono fun k l h =>
    h.mono Set.inter_subset_right Set.inter_subset_right
  have hTP : T = ⋃ k, P k := by
    rw [← Set.inter_iUnion, iUnion_disjointed, eq_comm, Set.inter_eq_left]
    intro y _
    have hy : y ∈ ⋃ j, (A.e j).source := Set.mem_iUnion.2 (A.cover y)
    rw [← hCU] at hy
    obtain ⟨l, hl, hy⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨k, rfl⟩ := hf.le (Set.mem_insert_of_mem _ hl)
    exact Set.mem_iUnion.2 ⟨k, hy⟩
  have hIm : ∀ k, MeasurableSet (Φ '' P k) := fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).1
  have hId : Pairwise (Disjoint on fun k => Φ '' P k) := by
    intro k l hkl
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have := hinj (hPΩ l hy) (hPΩ k hx) hxy
    subst this
    exact Set.disjoint_left.1 (hPd hkl) hx hy
  rw [hTP, Set.image_iUnion, measure_iUnion hPd hPm, lintegral_iUnion hIm hId]
  exact tsum_congr fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).2

end GlobalTheory.FlagCell2.ChangeOfVariables
