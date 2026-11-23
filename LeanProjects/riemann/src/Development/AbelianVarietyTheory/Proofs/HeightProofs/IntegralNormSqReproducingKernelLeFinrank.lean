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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

variable {n : ℕ}

theorem integral_star_mul_self {ε : Fin n → Bool} (f : KG ε → ℂ) :
    ∫ k, star (f k) * f k ∂(muK ε) = ((∫ k, ‖f k‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1; funext k
  rw [mul_comm, ← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj _

def l2InnerCore {ε : Fin n → Bool} (V : Submodule ℂ (KG ε → ℂ)) (hV : ∀ p ∈ V, Continuous p) :
    InnerProductSpace.Core ℂ V where
  inner p q := ∫ k, star (p.1 k) * q.1 k ∂(muK ε)
  conj_inner_symm p q := by
    rw [← integral_conj]
    congr 1; funext k
    simp [mul_comm]
  re_inner_nonneg p := by
    rw [integral_star_mul_self]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_nonneg fun k => by positivity
  add_left p q r := by
    have hp := hV _ p.2
    have hq := hV _ q.2
    have hr := hV _ r.2
    rw [← integral_add (integrable_of_continuousK (f := fun k => star (p.1 k) * r.1 k) (by fun_prop))
      (integrable_of_continuousK (f := fun k => star (q.1 k) * r.1 k) (by fun_prop))]
    congr 1; funext k
    simp [add_mul]
  smul_left p q c := by
    rw [← integral_const_mul]
    congr 1; funext k
    simp [mul_assoc]
  definite p h := by
    have hp := hV _ p.2
    have h0 : ∫ k, ‖p.1 k‖ ^ 2 ∂(muK ε) = 0 := by
      have h' : ∫ k, star (p.1 k) * p.1 k ∂(muK ε) = 0 := h
      rw [integral_star_mul_self] at h'
      exact_mod_cast h'
    have hns : Continuous (fun k => ‖p.1 k‖ ^ 2) := by fun_prop
    have h2 : (fun k => ‖p.1 k‖ ^ 2) =ᵐ[muK ε] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg _)
        ((integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re)).1 h0
    have h3 : (fun k => ‖p.1 k‖ ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq (muK ε) hns continuous_const).1 h2
    ext k
    simpa using congrFun h3 k

theorem exists_parseval {ε : Fin n → Bool} (V : Submodule ℂ (KG ε → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ p ∈ V, Continuous p) :
    ∃ φ : Fin (Module.finrank ℂ V) → KG ε → ℂ, (∀ j, φ j ∈ V) ∧ (∀ j, ∫ k, ‖φ j k‖ ^ 2 ∂(muK ε) = 1) ∧
      ∀ r ∈ V, ∫ k, ‖r k‖ ^ 2 ∂(muK ε) = ∑ j, ‖∫ k, star (r k) * φ j k ∂(muK ε)‖ ^ 2 := by
  letI c := l2InnerCore V hV
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hin : ∀ p q : V, inner ℂ p q = ∫ k, star (p.1 k) * q.1 k ∂(muK ε) := fun _ _ => rfl
  have hn : ∀ p : V, ∫ k, ‖p.1 k‖ ^ 2 ∂(muK ε) = ‖p‖ ^ 2 := by
    intro p
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) p
    rw [hin, integral_star_mul_self] at h
    apply Complex.ofReal_injective
    rw [h, Complex.ofReal_pow]
    rfl
  let b := stdOrthonormalBasis ℂ V
  refine ⟨fun j => (b j).1, fun j => (b j).2, fun j => ?_, fun r hr => ?_⟩
  · rw [hn, b.orthonormal.1 j, one_pow]
  · rw [hn ⟨r, hr⟩, ← b.sum_sq_norm_inner_left]
    rfl

theorem mul_left_mem_low {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ lowV ε i) :
    (fun k => φ (a * k)) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at h ⊢
    subst h
    rfl
  | succ j => exact mul_left_mem a h

def topV (ε : Fin n → Bool) (i : ℕ) : Submodule ℂ (KG ε → ℂ) where
  carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, fun q hq => ?_⟩
    have h1 := continuous_of_mem ha
    have h2 := continuous_of_mem hb
    have h3 := continuous_of_mem (lowV_le ε i hq)
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (integrable_of_continuousK (f := fun k => star (q k) * a k) (by fun_prop))
      (integrable_of_continuousK (f := fun k => star (q k) * b k) (by fun_prop)), ha' q hq, hb' q hq, add_zero]
  zero_mem' := ⟨zero_mem _, fun q _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
    have : (fun k => star (q k) * (c • a) k) = fun k => c * (star (q k) * a k) := by
      funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, integral_const_mul, ha' q hq, mul_zero]

theorem topV_le (ε : Fin n → Bool) (i : ℕ) : topV ε i ≤ polyV ε i := fun _ h => h.1

theorem mul_left_mem_top {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ topV ε i) :
    (fun k => φ (a * k)) ∈ topV ε i := by
  refine ⟨mul_left_mem a h.1, fun q hq => ?_⟩
  have h1 := h.2 _ (mul_left_mem_low a⁻¹ hq)
  rw [← integral_mul_left_eq_self (μ := muK ε) _ a] at h1
  simpa only [inv_mul_cancel_left] using h1

theorem star_mem_top {ε : Fin n → Bool} {i : ℕ} {e : KG ε → ℂ} (he : IsKer ε i e) :
    (fun k => star (e k)) ∈ topV ε i := by
  refine ⟨star_mem he.1, fun q hq => ?_⟩
  calc ∫ k, star (q k) * star (e k) ∂(muK ε)
      = ∫ k, (starRingEnd ℂ) (e k * q k) ∂(muK ε) := by
        congr 1; funext k; rw [map_mul, mul_comm]; rfl
    _ = (starRingEnd ℂ) (∫ k, e k * q k ∂(muK ε)) := integral_conj
    _ = 0 := by rw [he.2.1 q hq, map_zero]

theorem integral_norm_sq_ker_le : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e →
    ∫ k, ‖e k‖ ^ 2 ∂(muK ε) ≤ (Module.finrank ℂ (polyV ε i) : ℝ) := by
  intro n ε i e he
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : FiniteDimensional ℂ (topV ε i) := Submodule.finiteDimensional_of_le (topV_le ε i)
  obtain ⟨φ, hφ, h1, hP⟩ := exists_parseval (topV ε i) (fun p hp => continuous_of_mem hp.1)
  have key : ∀ a : KG ε, ∫ k, ‖e k‖ ^ 2 ∂(muK ε) = ∑ j, ‖φ j a‖ ^ 2 := by
    intro a
    have h := hP _ (mul_left_mem_top a⁻¹ (star_mem_top he))
    simp only [star_star, norm_star] at h
    rw [integral_mul_left_eq_self (μ := muK ε) (fun k => ‖e k‖ ^ 2) a⁻¹] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 := mul_left_mem_top a (hφ j)
    have h3 := he.2.2 _ h2.1 h2.2
    rw [← integral_mul_left_eq_self (μ := muK ε) _ a]
    simp only [inv_mul_cancel_left, mul_one] at h3 ⊢
    rw [h3]
  have hint : ∀ j, Integrable (fun a => ‖φ j a‖ ^ 2) (muK ε) := by
    intro j
    have hp := continuous_of_mem (hφ j).1
    have hns : Continuous (fun k => ‖φ j k‖ ^ 2) := by fun_prop
    exact (integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re
  calc ∫ k, ‖e k‖ ^ 2 ∂(muK ε) = ∫ _a, (∫ k, ‖e k‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by simp
    _ = ∫ a, ∑ j, ‖φ j a‖ ^ 2 ∂(muK ε) := by congr 1; funext a; exact key a
    _ = ∑ j, ∫ a, ‖φ j a‖ ^ 2 ∂(muK ε) := integral_finset_sum _ fun j _ => hint j
    _ = (Module.finrank ℂ (topV ε i) : ℝ) := by simp [h1]
    _ ≤ _ := by exact_mod_cast Submodule.finrank_mono (topV_le ε i)

end GlobalTheory.KFourier

end
