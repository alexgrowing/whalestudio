import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.FockJet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFockLSqLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockMoment

variable {ι : Type} [Fintype ι] {a b : ℕ}

def unitPt (r : ι → ℝ) (u : DVar ι a b → ℂ) : VCx ι a b := fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α)

def scalePt (r : ι → ℝ) (z : VCx ι a b) : DVar ι a b → ℂ := fun x => (r x.1 : ℂ) * z x.1 x.2.1 x.2.2

def scaleEquiv (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) : VCx ι a b ≃ᵐ (DVar ι a b → ℂ) where
  toFun := scalePt r
  invFun := unitPt r
  left_inv z := by
    funext τ β α
    have : (r τ : ℂ) ≠ 0 := by exact_mod_cast (hr τ).ne'
    simp [unitPt, scalePt, this]
  right_inv u := by
    funext x
    have : (r x.1 : ℂ) ≠ 0 := by exact_mod_cast (hr x.1).ne'
    simp [unitPt, scalePt, this]
  measurable_toFun := (show Continuous (scalePt (a := a) (b := b) r) by unfold scalePt; fun_prop).measurable
  measurable_invFun := (show Continuous (unitPt (a := a) (b := b) r) by unfold unitPt; fun_prop).measurable

theorem scaleEquiv_apply (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (z : VCx ι a b) :
    scaleEquiv r hr z = scalePt r z := rfl

theorem unitPt_scalePt (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (z : VCx ι a b) :
    unitPt r (scalePt r z) = z := (scaleEquiv r hr).symm_apply_apply z

theorem volume_eq_smul_map (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) :
    (volume : Measure (DVar ι a b → ℂ)) =
      ENNReal.ofReal (∏ x : DVar ι a b, r x.1 ^ 2) • (volume : Measure (VCx ι a b)).map (scaleEquiv r hr) := by
  rw [volume_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.map_apply (scaleEquiv r hr).measurable (MeasurableSet.univ_pi hs), smul_eq_mul]
  have e : (scaleEquiv r hr) ⁻¹' Set.univ.pi s = Set.univ.pi fun τ => Set.univ.pi fun β => Set.univ.pi fun α =>
      (fun w : ℂ => r τ • w) ⁻¹' s (τ, β, α) := by
    ext z
    simp [scaleEquiv_apply, scalePt, Set.mem_univ_pi, Prod.forall, Complex.real_smul]
  rw [e, volume_pi, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [ENNReal.ofReal_prod_of_nonneg (fun x _ => sq_nonneg _)]
  simp_rw [Fintype.prod_prod_type]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun α _ => ?_
  rw [Measure.addHaar_preimage_smul _ (hr τ).ne', Complex.finrank_real_complex, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg _), abs_of_pos (by have := hr τ; positivity), mul_inv_cancel₀ (by have := hr τ; positivity),
    ENNReal.ofReal_one, one_mul]

theorem integral_unitPt (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (h : VCx ι a b → ℂ) :
    ∫ u : DVar ι a b → ℂ, h (unitPt r u) = ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) * ∫ z, h z := by
  rw [volume_eq_smul_map r hr, integral_smul_measure, integral_map_equiv]
  have hP : 0 ≤ ∏ x : DVar ι a b, r x.1 ^ 2 := Finset.prod_nonneg fun _ _ => sq_nonneg _
  rw [ENNReal.toReal_ofReal hP, Complex.real_smul]
  simp only [scaleEquiv_apply, unitPt_scalePt r hr]

end GlobalTheory.FockMoment

namespace GlobalTheory.FockMoment

open Formalism.DimensionVariation (nsq mono cj mfact)

theorem gaussMoment : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z) : ℂ) * G z = ((∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) : ℂ) * ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) * derivAt0 G m := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ m
  classical
  set r : ι → ℝ := fun τ => Real.sqrt (c τ) with hr_def
  have hr : ∀ τ, 0 < r τ := fun τ => Real.sqrt_pos.2 (hc τ)
  have hr2 : ∀ τ, r τ ^ 2 = c τ := fun τ => Real.sq_sqrt (hc τ).le
  have hrC : ∀ τ, (r τ : ℂ) ≠ 0 := fun τ => by exact_mod_cast (hr τ).ne'
  set F : (DVar ι a b → ℂ) → ℂ := fun u => G fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α) with hF_def
  have hFd : Differentiable ℂ F := hG.comp (by fun_prop)
  have hgq : ∀ u : DVar ι a b → ℂ, gq c (unitPt r u) = nsq u := by
    intro u
    simp only [gq, unitPt, nsq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, hr2, ← mul_assoc,
      mul_inv_cancel₀ (hc τ).ne', one_mul]
  have hmono : ∀ u : DVar ι a b → ℂ, conjMono m (unitPt r u) =
      (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * mono (Formalism.DimensionVariation.cj u) m := by
    intro u
    rw [conjMono, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [unitPt, Formalism.DimensionVariation.cj, mul_pow, Complex.conj_ofReal]
  have hgrow : ∀ u : DVar ι a b → ℂ, ‖F u‖ ≤ M * Real.exp (nsq u / 2) := fun u => by
    rw [← hgq u]; exact hM _
  have hfj := (Formalism.DimensionVariation.gaussianCoeffIntegral (DVar ι a b) F (GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F) M hFd.continuous
    (GlobalTheory.JetFrameCompare.hasSum_taylorCoeff hFd) hgrow m).2
  have htj := GlobalTheory.JetBlock.taylor_jetC hG r hr (fun _ => 1) m
  simp only [Formalism.L2.Ker.jetC, one_pow, one_mul] at htj
  rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Finset.prod_const_one, one_mul] at htj
  have hcov := integral_unitPt r hr (fun z => conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hint : ∫ u : DVar ι a b → ℂ, conjMono m (unitPt r u) * (Real.exp (-gq c (unitPt r u)) : ℂ) * G (unitPt r u) =
      (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * ∫ u, F u * mono (Formalism.DimensionVariation.cj u) m * (Real.exp (-(nsq u)) : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext u
    have hFu : F u = G (unitPt r u) := rfl
    rw [hmono, hgq, hFu]
    ring
  rw [hint, hfj] at hcov
  have htj' : GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) * ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x = derivAt0 G m := htj
  have hPpos : 0 < ∏ x : DVar ι a b, r x.1 ^ 2 := Finset.prod_pos fun x _ => by have := hr x.1; positivity
  have hP : (∏ x : DVar ι a b, r x.1 ^ 2) = ∏ x : DVar ι a b, c x.1 := Finset.prod_congr rfl fun x _ => hr2 x.1
  have hpi : (∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) =
      Real.pi ^ Fintype.card (DVar ι a b) * (∏ x : DVar ι a b, r x.1 ^ 2)⁻¹ := by
    rw [hP]
    simp only [Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod]
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, div_eq_mul_inv, mul_comm b a,
      mul_comm (a * b) (Fintype.card ι)]
  have hmp : ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) = (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) ^ 2 := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    push_cast
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← hr2 x.1]
    push_cast
    ring
  have hPC : ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hRR : (∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x) * (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => by rw [← mul_pow, mul_inv_cancel₀ (hrC x.1), one_pow]
  have hPinv := mul_inv_cancel₀ hPC
  rw [hpi, hmp, ← htj']
  apply mul_left_cancel₀ hPC
  rw [← hcov, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  set P := ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) with hP_def
  set R := ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x with hR_def
  set Ri := ∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x with hRi_def
  set TM := GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) with hTM
  set K := (Real.pi : ℂ) ^ Fintype.card (DVar ι a b) with hK
  linear_combination (-(K * TM * Ri)) * hRR + (-(K * TM * Ri ^ 2 * R)) * hPinv
