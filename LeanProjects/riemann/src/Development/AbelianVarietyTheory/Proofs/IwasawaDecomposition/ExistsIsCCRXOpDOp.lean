import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculusStatement

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.Ccr

theorem comm_comb {A : Type} [Ring A] [Algebra ℂ A] (p p' q q' : A) (s t c₁ c₂ c₃ c₄ : ℂ)
    (h₁ : p * q = q * p + c₁ • (1 : A)) (h₂ : p * q' = q' * p + c₂ • (1 : A))
    (h₃ : p' * q = q * p' + c₃ • (1 : A)) (h₄ : p' * q' = q' * p' + c₄ • (1 : A)) :
    (p + s • p') * (q + t • q') = (q + t • q') * (p + s • p') + (c₁ + t * c₂ + s * c₃ + s * t * c₄) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h₁, h₂, h₃, h₄]
  module

theorem exists_om {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) :
    ∃ om : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ, ∀ x y, om x y = (star y ⬝ᵥ H *ᵥ x).im := by
  let b : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
    (fun x x' y => by simp [mulVec_add, dotProduct_add])
    (fun r x y => by simp [mulVec_smul, dotProduct_smul])
    (fun x y y' => by simp [add_dotProduct])
    (fun r x y => by simp [smul_dotProduct])
  exact ⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ b), fun x y => rfl⟩

theorem im_self {ι : Type} [Fintype ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (x : ι → ℂ) :
    (star x ⬝ᵥ H *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ H *ᵥ x) = star x ⬝ᵥ H *ᵥ x := by
    rw [← star_dotProduct_star, star_star, star_mulVec, hH, dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem pair_inv {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (k l : ι) :
    star (H⁻¹ *ᵥ Pi.single l 1) ⬝ᵥ H *ᵥ Pi.single k 1 = if k = l then (1 : ℂ) else 0 := by
  rw [star_mulVec, conjTranspose_nonsing_inv, hH, ← dotProduct_mulVec, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), one_mulVec, dotProduct_single]
  by_cases h : k = l <;> simp [h]

end GlobalTheory.Mem.Lift.Ccr

open GlobalTheory.Mem.Lift.Ccr in

theorem GlobalTheory.Mem.Lift.exists_isCCR_xOp_dOp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∃ x d : ι → Module.End ℂ (smS ρ), (∀ k f, (x k f).1 = xOp ρ k f.1) ∧ (∀ k f, (d k f).1 = dOp ρ H k f.1) ∧ IsCCR x d := by
  intro ι _ _ H hH hd B _ _ ρ hρ
  obtain ⟨om, hom⟩ := exists_om H
  have hρ' : IsHeis (fun x y => om x y) ρ := by simpa only [hom] using hρ
  have key := GlobalTheory.T.heisenbergSmoothVector_derivative_calculus (ι → ℂ) B om ρ (fun x => by rw [hom, im_self hH]) hρ'
  let D : (ι → ℂ) → Module.End ℂ (smS ρ) := fun v =>
    { toFun := fun f => ⟨dH ρ v f.1, (key f.1 f.2).1 v⟩
      map_add' := fun f g => Subtype.ext (dH_add v f.2 g.2)
      map_smul' := fun a f => Subtype.ext (dH_smul v a f.2) }
  have hD : ∀ u v, D u * D v = D v * D u + (2 * π * I * ((star v ⬝ᵥ H *ᵥ u).im : ℂ)) • (1 : Module.End ℂ (smS ρ)) := by
    intro u v
    refine LinearMap.ext fun f => Subtype.ext ?_
    have := (key f.1 f.2).2.2.2.2 u v
    rw [hom, sub_eq_iff_eq_add'] at this
    exact this
  have hc : ∀ (u v : ι → ℂ) (s t : ℂ), (D u + s • D (I • u)) * (D v + t • D (I • v)) =
      (D v + t • D (I • v)) * (D u + s • D (I • u)) +
        (2 * π * I * ((1 + s * t) * (star v ⬝ᵥ H *ᵥ u).im + (s - t) * (star v ⬝ᵥ H *ᵥ u).re)) •
          (1 : Module.End ℂ (smS ρ)) := by
    intro u v s t
    rw [comm_comb _ _ _ _ s t _ _ _ _ (hD u v) (hD u (I • v)) (hD (I • u) v) (hD (I • u) (I • v))]
    congr 2
    simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    simp
    ring
  have hII : (1 : ℂ) + I * I = 0 := by simp
  refine ⟨fun k => D (Pi.single k 1) + (-I) • D (I • Pi.single k 1),
    fun l => (-(1 / (4 * π)) : ℂ) • (D (H⁻¹ *ᵥ Pi.single l 1) + I • D (I • H⁻¹ *ᵥ Pi.single l 1)),
    fun k f => ?_, fun k f => rfl, fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
  · rw [xOp, sub_eq_add_neg, ← neg_smul]
    rfl
  · beta_reduce
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc (Pi.single k 1), pair_inv hH hd, ← smul_sub, sub_add_cancel_left, ← neg_smul, smul_smul]
    by_cases h : k = l
    · simp only [h, if_true, one_im, one_re, ofReal_zero, ofReal_one]
      have hp : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have : (-(1 / (4 * π)) : ℂ) * -(2 * π * I * ((1 + -I * I) * 0 + (-I - I) * 1)) = 1 := by
        field_simp
        linear_combination (-4) * hII
      rw [this, one_smul]
    · simp [h]
