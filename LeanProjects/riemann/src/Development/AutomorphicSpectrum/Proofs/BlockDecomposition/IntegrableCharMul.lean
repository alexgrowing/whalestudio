import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureTensorDecompositionLocal
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitGauss

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem trace_swap (u z : F × F) :
    Algebra.trace F (F × F) (swapE u * z) = z.1 * u.2 + z.2 * u.1 := by
  have h : ∀ x : F × F, Algebra.trace F (F × F) x = x.1 + x.2 := fun x => by
    rw [Algebra.trace_prod]; simp
  rw [h]
  show u.2 * z.1 + u.1 * z.2 = _
  ring

theorem integrable_sb {χ : AddChar F Circle} (hχ : Continuous χ) {f : F → ℂ}
    (hf : f ∈ schwartzBruhat F) : Integrable f (selfDualMeasure χ) := by
  have h := integrable_mul_char_of_mem_schwartzBruhat (selfDualMeasure χ) hχ hf 0
  simpa using h

theorem continuous_char {χ : AddChar F Circle} (hχ : Continuous χ) {X : Type*} [TopologicalSpace X]
    {k : X → F} (hk : Continuous k) : Continuous fun x => (χ (k x) : ℂ) :=
  continuous_subtype_val.comp (hχ.comp hk)

theorem integrable_char_mul {χ : AddChar F Circle} (hχ : Continuous χ) {ν : Measure (F × F)}
    {k : F × F → F} (hk : Continuous k) {h : F × F → ℂ} (hh : Integrable h ν) :
    Integrable (fun u => (χ (k u) : ℂ) * h u) ν := by
  refine hh.mono ((continuous_char hχ hk).aestronglyMeasurable.mul hh.1) (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_mul, Circle.norm_coe, one_mul]

theorem fts_sum {χ : AddChar F Circle} (hχ : Continuous χ) {n : ℕ} {f g : Fin n → F → ℂ}
    (hf : ∀ i, f i ∈ schwartzBruhat F) (hg : ∀ i, g i ∈ schwartzBruhat F) (u : F × F) :
    FTs χ swapE (muS χ) (fun z => ∑ i, f i z.1 * g i z.2) u =
      ∑ i, localFourier (selfDualMeasure χ) χ (f i) u.2 *
        localFourier (selfDualMeasure χ) χ (g i) u.1 := by
  have e : ∀ z : F × F, (∑ i, f i z.1 * g i z.2) * (χ (Algebra.trace F (F × F) (swapE u * z)) : ℂ) =
      ∑ i, (f i z.1 * (χ (z.1 * u.2) : ℂ)) * (g i z.2 * (χ (z.2 * u.1) : ℂ)) := by
    intro z
    rw [trace_swap, AddChar.map_add_eq_mul, Circle.coe_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold FTs
  simp only [e]
  rw [integral_finset_sum _ fun i _ => Integrable.mul_prod
    (integrable_mul_char_of_mem_schwartzBruhat _ hχ (hf i) u.2)
    (integrable_mul_char_of_mem_schwartzBruhat _ hχ (hg i) u.1)]
  exact Finset.sum_congr rfl fun i _ =>
    integral_prod_mul (fun x => f i x * (χ (x * u.2) : ℂ)) (fun x => g i x * (χ (x * u.1) : ℂ))

theorem left_term {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (a : F) {f g : F → ℂ}
    (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    Integrable (fun u : F × F => (χ (a * (u.1 * u.2)) : ℂ) *
      (localFourier (selfDualMeasure χ) χ f u.2 * localFourier (selfDualMeasure χ) χ g u.1)) (muS χ) ∧
    ∫ u : F × F, (χ (a * (u.1 * u.2)) : ℂ) *
      (localFourier (selfDualMeasure χ) χ f u.2 * localFourier (selfDualMeasure χ) χ g u.1) ∂muS χ =
      ∫ x, localFourier (selfDualMeasure χ) χ g x * f (-(a * x)) ∂selfDualMeasure χ := by
  have hT := fun {h : F → ℂ} (hh : h ∈ schwartzBruhat F) =>
    localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hh
  have hb : Integrable (fun u : F × F => localFourier (selfDualMeasure χ) χ f u.2 *
      localFourier (selfDualMeasure χ) χ g u.1) (muS χ) := by
    have := Integrable.mul_prod (integrable_sb hχ (hT hg)) (integrable_sb hχ (hT hf))
    simpa only [mul_comm] using this
  have hI := integrable_char_mul hχ (k := fun u : F × F => a * (u.1 * u.2)) (by fun_prop) hb
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h := localFourier_localFourier_selfDual hχ hχ1 hf (a * x)
  show ∫ y, (χ (a * (x * y)) : ℂ) * (localFourier (selfDualMeasure χ) χ f y *
    localFourier (selfDualMeasure χ) χ g x) ∂selfDualMeasure χ = _ * f (-(a * x))
  have h2 : localFourier (selfDualMeasure χ) χ (localFourier (selfDualMeasure χ) χ f) (a * x) =
      ∫ y, localFourier (selfDualMeasure χ) χ f y * (χ (y * (a * x)) : ℂ) ∂selfDualMeasure χ := rfl
  rw [← h, h2, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e : a * (x * y) = y * (a * x) := by ring
  simp only [e]
  ring

theorem right_term {χ : AddChar F Circle} (hχ : Continuous χ) {a : F} (ha : a ≠ 0) {f g : F → ℂ}
    (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    Integrable (fun z : F × F => (χ (-(z.1 * z.2) / a) : ℂ) * (f z.1 * g z.2)) (muS χ) ∧
    ∫ z : F × F, (χ (-(z.1 * z.2) / a) : ℂ) * (f z.1 * g z.2) ∂muS χ =
      ∫ x, f x * localFourier (selfDualMeasure χ) χ g (-x / a) ∂selfDualMeasure χ := by
  have hb : Integrable (fun z : F × F => f z.1 * g z.2) (muS χ) :=
    Integrable.mul_prod (integrable_sb hχ hf) (integrable_sb hχ hg)
  have hI := integrable_char_mul hχ (k := fun z : F × F => -(z.1 * z.2) / a)
    (by have : Continuous fun z : F × F => -(z.1 * z.2) * a⁻¹ := by fun_prop
        simpa only [div_eq_mul_inv] using this) hb
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∫ y, (χ (-(x * y) / a) : ℂ) * (f x * g y) ∂selfDualMeasure χ =
    f x * localFourier (selfDualMeasure χ) χ g (-x / a)
  have h2 : localFourier (selfDualMeasure χ) χ g (-x / a) =
      ∫ y, g y * (χ (y * (-x / a)) : ℂ) ∂selfDualMeasure χ := rfl
  rw [h2, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e : -(x * y) / a = y * (-x / a) := by ring
  simp only [e]
  ring

theorem subst_term (χ : AddChar F Circle) {a : F} (ha : a ≠ 0) (f g : F → ℂ) :
    ∫ x, localFourier (selfDualMeasure χ) χ g x * f (-(a * x)) ∂selfDualMeasure χ =
      (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ x, f x * localFourier (selfDualMeasure χ) χ g (-x / a) ∂selfDualMeasure χ := by
  set h : F → ℂ := fun x => f x * localFourier (selfDualMeasure χ) χ g (-x / a) with hh
  have e := integral_comp_mul_left (selfDualMeasure χ) ha (fun y => h (-y))
  rw [integral_neg_eq_self h, Complex.real_smul] at e
  rw [← e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e2 : - -(a * x) / a = x := by field_simp
  simp only [hh, e2]
  ring

theorem sGauss : SGauss := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 a Φ hΦ
  obtain ⟨n, f, g, hf, hg, hfg⟩ := GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hΦ.1 hΦ.2
  have hf' : ∀ i, f i ∈ schwartzBruhat F := hf
  have hg' : ∀ i, g i ∈ schwartzBruhat F := hg
  obtain rfl : Φ = fun z => ∑ i, f i z.1 * g i z.2 := funext fun z => hfg z.1 z.2
  have ha : (a : F) ≠ 0 := a.ne_zero
  calc ∫ u, (χ ((a : F) * (u.1 * u.2)) : ℂ) * FTs χ swapE (muS χ) (fun z => ∑ i, f i z.1 * g i z.2) u ∂muS χ
      = ∫ u : F × F, ∑ i, (χ ((a : F) * (u.1 * u.2)) : ℂ) *
          (localFourier (selfDualMeasure χ) χ (f i) u.2 * localFourier (selfDualMeasure χ) χ (g i) u.1) ∂muS χ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show _ * _ = _
        rw [fts_sum hχ hf' hg', Finset.mul_sum]
    _ = ∑ i, ∫ x, localFourier (selfDualMeasure χ) χ (g i) x * f i (-((a : F) * x)) ∂selfDualMeasure χ := by
        rw [integral_finset_sum _ fun i _ => (left_term hχ hχ1 a (hf' i) (hg' i)).1]
        exact Finset.sum_congr rfl fun i _ => (left_term hχ hχ1 a (hf' i) (hg' i)).2
    _ = (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) *
          ∑ i, ∫ x, f i x * localFourier (selfDualMeasure χ) χ (g i) (-x / a) ∂selfDualMeasure χ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => subst_term χ ha (f i) (g i)
    _ = (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) *
          ∫ z, (χ (-(z.1 * z.2) / a) : ℂ) * ∑ i, f i z.1 * g i z.2 ∂muS χ := by
        congr 1
        simp only [Finset.mul_sum]
        rw [integral_finset_sum _ fun i _ => (right_term hχ ha (hf' i) (hg' i)).1]
        exact Finset.sum_congr rfl fun i _ => (right_term hχ ha (hf' i) (hg' i)).2.symm

end GlobalTheory.CompanionTheory.SplitGauss
