import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integral_conjK (ε : Fin n → Bool) (f : KG ε → ℂ) (a : KG ε) :
    ∫ k, f (a * k * a⁻¹) ∂(muK ε) = ∫ k, f k ∂(muK ε) := by
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  have h1 := integral_mul_right_eq_self (μ := muK ε) (fun k => f (a * k)) a⁻¹
  have h2 := integral_mul_left_eq_self (μ := muK ε) f a
  simp only [mul_assoc] at h1 ⊢
  exact h1.trans h2

theorem integrable_of_continuousK {ε : Fin n → Bool} {f : KG ε → ℂ} (hf : Continuous f) :
    Integrable f (muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem lowV_le (ε : Fin n → Bool) (i : ℕ) : lowV ε i ≤ polyV ε i := by
  cases i with
  | zero => exact bot_le
  | succ j => exact polyV_mono ε (Nat.le_succ j)

theorem integral_sub_mulK {ε : Fin n → Bool} {f g h : KG ε → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    ∫ k, (f - g) k * h k ∂(muK ε) = ∫ k, f k * h k ∂(muK ε) - ∫ k, g k * h k ∂(muK ε) := by
  rw [← integral_sub (integrable_of_continuousK (f := fun k => f k * h k) (hf.mul hh))
    (integrable_of_continuousK (f := fun k => g k * h k) (hg.mul hh))]
  congr 1; funext k; simp [sub_mul]

theorem isKer_unique {ε : Fin n → Bool} {i : ℕ} {e e' : KG ε → ℂ} (he : IsKer ε i e) (he' : IsKer ε i e') :
    e = e' := by
  have hdmem : (e - e') ∈ polyV ε i := sub_mem he.1 he'.1
  have hc : Continuous (e - e') := continuous_of_mem hdmem
  have hce : Continuous e := continuous_of_mem he.1
  have hce' : Continuous e' := continuous_of_mem he'.1
  have hp : (fun k => star ((e - e') k)) ∈ polyV ε i := star_mem hdmem
  have horth : ∀ q ∈ lowV ε i, ∫ k, star (q k) * star ((e - e') k) ∂(muK ε) = 0 := by
    intro q hq
    have hqc : Continuous q := continuous_of_mem (lowV_le ε i hq)
    have h1 := he.2.1 q hq
    have h2 := he'.2.1 q hq
    have h3 : ∫ k, (e - e') k * q k ∂(muK ε) = 0 := by
      rw [integral_sub_mulK hce hce' hqc, h1, h2, sub_self]
    calc ∫ k, star (q k) * star ((e - e') k) ∂(muK ε)
        = ∫ k, (starRingEnd ℂ) ((e - e') k * q k) ∂(muK ε) := by
          congr 1; funext k; rw [map_mul, mul_comm]; rfl
      _ = (starRingEnd ℂ) (∫ k, (e - e') k * q k ∂(muK ε)) := integral_conj
      _ = 0 := by rw [h3, map_zero]
  have h0 : ∫ k, (e - e') k * star ((e - e') k) ∂(muK ε) = 0 := by
    have a1 := he.2.2 _ hp horth
    have a2 := he'.2.2 _ hp horth
    have hs : Continuous (fun k => star ((e - e') k)) := continuous_star.comp hc
    rw [integral_sub_mulK hce hce' hs, a1, a2, sub_self]
  have hns : Continuous (fun k => Complex.normSq ((e - e') k)) := Complex.continuous_normSq.comp hc
  have h1 : ∫ k, Complex.normSq ((e - e') k) ∂(muK ε) = 0 := by
    have : (fun k => (e - e') k * star ((e - e') k)) = fun k => ((Complex.normSq ((e - e') k) : ℝ) : ℂ) :=
      funext fun k => Complex.mul_conj _
    rw [this, integral_complex_ofReal] at h0
    exact_mod_cast h0
  have h2 : (fun k => Complex.normSq ((e - e') k)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _)
      ((integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re)).1 h1
  have h3 : (fun k => Complex.normSq ((e - e') k)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hns continuous_const).1 h2
  funext k
  have := congrFun h3 k
  simp only [Pi.zero_apply, map_eq_zero, Pi.sub_apply] at this
  exact sub_eq_zero.1 this

theorem conj_mem {ε : Fin n → Bool} (a : KG ε) {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => φ (a * k * a⁻¹)) ∈ polyV ε d := by
  have := mul_right_mem a⁻¹ (mul_left_mem a h)
  simpa only [mul_assoc] using this

theorem conj_mem_low {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ lowV ε i) :
    (fun k => φ (a * k * a⁻¹)) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at h ⊢
    subst h
    rfl
  | succ j => exact conj_mem a h

theorem isKer_conj {ε : Fin n → Bool} {i : ℕ} {e : KG ε → ℂ} (he : IsKer ε i e) (a : KG ε) :
    IsKer ε i (fun k => e (a * k * a⁻¹)) := by
  have key : ∀ f g : KG ε → ℂ, ∫ k, f (a * k * a⁻¹) * g k ∂(muK ε) = ∫ k, f k * g (a⁻¹ * k * a) ∂(muK ε) := by
    intro f g
    rw [← integral_conjK ε (fun k => f k * g (a⁻¹ * k * a)) a]
    congr 1; funext k
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  refine ⟨conj_mem a he.1, ?_, ?_⟩
  · intro q hq
    rw [key]
    have := conj_mem_low a⁻¹ hq
    simpa only [inv_inv] using he.2.1 _ this
  · intro p hp horth
    rw [key]
    have hp' : (fun k => p (a⁻¹ * k * a)) ∈ polyV ε i := by simpa only [inv_inv] using conj_mem a⁻¹ hp
    have horth' : ∀ q ∈ lowV ε i, ∫ k, star (q k) * p (a⁻¹ * k * a) ∂(muK ε) = 0 := by
      intro q hq
      rw [← integral_conjK ε (fun k => star (q k) * p (a⁻¹ * k * a)) a]
      have := horth _ (conj_mem_low a hq)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
    rw [he.2.2 _ hp' horth']
    simp

theorem isKer_class : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e →
    ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  intro n ε i e he a k
  have := isKer_unique (isKer_conj he a) he
  exact congrFun this k

end GlobalTheory.KFourier

end
