import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

private theorem hessC_congr_of_eventuallyEq' {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : f =ᶠ[𝓝 z] g) : ReciprocityTheory.AnForm.hessC f z = ReciprocityTheory.AnForm.hessC g z := by
  have h2 : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ g) z := (h.fderiv (𝕜 := ℝ)).fderiv_eq
  unfold ReciprocityTheory.AnForm.hessC
  rw [h2]

private theorem maDens_congr_of_hessC_eq {D : ℕ} {f g : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, f k =ᶠ[𝓝 z] g k) : ReciprocityTheory.AnForm.maDens f z = ReciprocityTheory.AnForm.maDens g z := by
  unfold ReciprocityTheory.AnForm.maDens
  rw [show (fun k => ReciprocityTheory.AnForm.hessC (f k) z) = (fun k => ReciprocityTheory.AnForm.hessC (g k) z) from
    funext fun k => hessC_congr_of_eventuallyEq' (h k)]

theorem paramDens_eq_normSq_mul_locDens {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) {V : Set (Fin e → ℂ)} {Φ : (Fin e → ℂ) → X} (P : Fin e → LocPot X)
    (j : Fin A.n) (hΦ : IsParam A V Φ) {z : Fin e → ℂ} (hzV : z ∈ V)
    (hz : Φ z ∈ (A.chart j).source) (hc : ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) :
    paramDens P Φ z = Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart j ∘ Φ) z).det *
      locDens A P j ((A.chart j ∘ Φ) z) := by
  have hcont : ContinuousAt Φ z := hΦ.2.1.continuousAt (hΦ.1.mem_nhds hzV)
  have hev : ∀ᶠ z' in 𝓝 z, Φ z' ∈ (A.chart j).source :=
    hcont.preimage_mem_nhds ((A.chart j).open_source.mem_nhds hz)
  have han : AnalyticAt ℂ (A.chart j ∘ Φ) z := hΦ.2.2.2 j z ⟨hzV, hz⟩
  have hinv : (A.chart j).symm ((A.chart j ∘ Φ) z) = Φ z := (A.chart j).left_inv hz
  have key := ReciprocityTheory.AnForm.A.maDens_comp (fun k => (P k).φ (Φ z) ∘ (A.chart j).symm)
    (A.chart j ∘ Φ) z han (fun k => hc k j hz)
  have h1 : paramDens P Φ z = ReciprocityTheory.AnForm.maDens
      (fun k => ((P k).φ (Φ z) ∘ (A.chart j).symm) ∘ (A.chart j ∘ Φ)) z := by
    unfold paramDens
    apply maDens_congr_of_hessC_eq
    intro k
    filter_upwards [hev] with z' hz'
    simp only [Function.comp_apply, (A.chart j).left_inv hz']
  have h2 : locDens A P j ((A.chart j ∘ Φ) z) = ReciprocityTheory.AnForm.maDens
      (fun k => (P k).φ (Φ z) ∘ (A.chart j).symm) ((A.chart j ∘ Φ) z) := by
    unfold ReciprocityTheory.AnForm.M.locDens
    rw [hinv]
    rfl
  rw [h1, key, h2, mul_comm]

theorem param_chart_changeOfVariables : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (j : Fin A.n), IsParam A V Φ → MeasurableSet B → B ⊆ V → (∀ z ∈ B, Φ z ∈ (A.chart j).source) → (∀ z ∈ B, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) → MeasurableSet ((A.chart j ∘ Φ) '' B) ∧ (IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A P j y) ((A.chart j ∘ Φ) '' B) ↔ IntegrableOn (fun z => g (Φ z) * paramDens P Φ z) B) ∧ ∫ y in (A.chart j ∘ Φ) '' B, g ((A.chart j).symm y) * locDens A P j y = ∫ z in B, g (Φ z) * paramDens P Φ z := by
  intro e X _ _ _ A V B Φ P g j hΦ hB hBV hsrc hc2
  have han : ∀ z ∈ B, AnalyticAt ℂ (A.chart j ∘ Φ) z := fun z hz => hΦ.2.2.2 j z ⟨hBV hz, hsrc z hz⟩
  have hτd : ∀ z ∈ B, HasFDerivWithinAt (A.chart j ∘ Φ)
      ((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ) B z := fun z hz =>
    ((han z hz).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn (A.chart j ∘ Φ) B := by
    intro x hx y hy hxy
    apply hΦ.2.2.1 (hBV hx) (hBV hy)
    have h := congrArg (A.chart j).symm hxy
    simpa only [Function.comp_apply, (A.chart j).left_inv (hsrc x hx),
      (A.chart j).left_inv (hsrc y hy)] using h
  have hdet : ∀ z ∈ B, |((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ).det| =
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart j ∘ Φ) z).det := by
    intro z hz
    rw [← ((han z hz).differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv,
      ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq _ _ (han z hz).differentiableAt]
    exact abs_of_nonneg (Complex.normSq_nonneg _)
  have hpt : Set.EqOn (fun z => |((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ).det| •
      (g ((A.chart j).symm ((A.chart j ∘ Φ) z)) * locDens A P j ((A.chart j ∘ Φ) z)))
      (fun z => g (Φ z) * paramDens P Φ z) B := by
    intro z hz
    simp only
    rw [hdet z hz, smul_eq_mul,
      paramDens_eq_normSq_mul_locDens A P j hΦ (hBV hz) (hsrc z hz) (hc2 z hz)]
    have hl : (A.chart j).symm ((A.chart j ∘ Φ) z) = Φ z := (A.chart j).left_inv (hsrc z hz)
    rw [hl]
    ring
  refine ⟨measurable_image_of_fderivWithin hB hτd hinj, ?_, ?_⟩
  · rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hB hτd hinj]
    exact integrableOn_congr_fun hpt hB
  · rw [integral_image_eq_integral_abs_det_fderiv_smul volume hB hτd hinj]
    exact setIntegral_congr_fun hB hpt

end GlobalTheory.CompanionTheory.Ar.PB
