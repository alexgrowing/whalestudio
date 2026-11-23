import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculus

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

noncomputable section

namespace GlobalTheory.Mem.Lift.Normal

variable {ι : Type}

theorem real_lin_smul (l : (ι → ℂ) →ₗ[ℝ] ℂ) (c : ℂ) (z : ι → ℂ) :
    l (c • z) = c.re * l z + c.im * l (I • z) := by
  have hc : c • z = c.re • z + c.im • (I • z) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  rw [hc, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem real_lin_I_I (l : (ι → ℂ) →ₗ[ℝ] ℂ) (z : ι → ℂ) : l (I • I • z) = - l z := by
  rw [smul_smul, I_mul_I, neg_one_smul, map_neg]

def linPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := l z - I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, RingHom.id_apply, smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (c.im * l (I • z)) * I_mul_I

def antiPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ⋆[ℂ] ℂ where
  toFun z := l z + I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, smul_eq_mul]
    have : (starRingEnd ℂ) c = c.re - c.im * I := by
      apply Complex.ext <;> simp
    rw [this]
    linear_combination (c.im * l (I • z)) * I_mul_I

theorem im_add_I_re (h : ℂ) : ((h.im : ℂ) + I * ((I * h).im : ℂ)) = I * (starRingEnd ℂ) h := by
  apply Complex.ext <;> simp

theorem im_sub_I_re (h : ℂ) : ((h.im : ℂ) - I * ((I * h).im : ℂ)) = - I * h := by
  apply Complex.ext <;> simp

variable [Fintype ι] [DecidableEq ι]

def nC (X : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ℂ :=
  X i.1 i.2.1 * (-(1 / (4 * π))) * (if i.2.2.1 then -I else 1) * (if i.2.2.2 then I else 1)

def nP (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.1 then I • Pi.single i.1 1 else Pi.single i.1 1

def nQ (H : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.2 then I • H⁻¹ *ᵥ Pi.single i.2.1 1 else H⁻¹ *ᵥ Pi.single i.2.1 1

theorem sum_lin (X : Matrix ι ι ℂ) (A : (ι → ℂ) →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * (v j * A (Pi.single k 1)) = A (X *ᵥ v) := by
  have hx : X *ᵥ v = ∑ k, (∑ j, X k j * v j) • (Pi.single k (1 : ℂ) : ι → ℂ) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_anti {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0)
    (A : (ι → ℂ) →ₗ⋆[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1)) = - A (X *ᵥ v) := by
  have hinv' : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hd)
  set w := X *ᵥ v with hw

  have hexp : w = ∑ j, (H *ᵥ w) j • (H⁻¹ *ᵥ Pi.single j 1) := by
    have h1 : H *ᵥ w = ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    calc w = H⁻¹ *ᵥ (H *ᵥ w) := by rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
      _ = H⁻¹ *ᵥ ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by rw [← h1]
      _ = _ := by
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul]
  have hA : A w = ∑ j, (starRingEnd ℂ) ((H *ᵥ w) j) * A (H⁻¹ *ᵥ Pi.single j 1) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smulₛₗ, smul_eq_mul]

  have hcoef : ∀ j, ∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1) = -(starRingEnd ℂ) ((H *ᵥ w) j) := by
    intro j
    have hs : ∀ k, star v ⬝ᵥ H *ᵥ Pi.single k 1 = (star v ᵥ* H) k := by
      intro k
      rw [Matrix.dotProduct_mulVec]
      simp [dotProduct, Pi.single_apply]
    have hXH : (H * X)ᴴ = -(H * X) := by
      rw [Matrix.conjTranspose_mul, hH]
      exact eq_neg_of_add_eq_zero_left hX
    have hstar : (starRingEnd ℂ) ((H *ᵥ w) j) = (star v ᵥ* (H * X)ᴴ) j := by
      rw [hw, Matrix.mulVec_mulVec, ← Matrix.star_mulVec]
      rfl
    simp_rw [hs]
    rw [hstar, hXH, Matrix.vecMul_neg, Pi.neg_apply, neg_neg, ← Matrix.vecMul_vecMul]
    simp [vecMul, dotProduct, mul_comm]
  rw [hA, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ k, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1))
      = (∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1)) * A (H⁻¹ *ᵥ Pi.single j 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        rw [hcoef j]
        ring

theorem isQuadOf_normal {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0) :
    IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) (nC X) nP (nQ H) := by
  intro l v
  beta_reduce
  have hinv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hd)

  have hkj : ∀ k j, (∑ b1 : Bool, ∑ b2 : Bool, nC X (k, j, b1, b2) *
      (((star v ⬝ᵥ H *ᵥ nQ H (k, j, b1, b2)).im : ℂ) * l (nP (k, j, b1, b2)) +
        ((star v ⬝ᵥ H *ᵥ nP (k, j, b1, b2)).im : ℂ) * l (nQ H (k, j, b1, b2)))) =
      X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
        (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    intro k j
    have ha : ((star v ⬝ᵥ H *ᵥ (H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) +
        I * ((star v ⬝ᵥ H *ᵥ (I • H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) = I * v j := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_add_I_re, Matrix.mulVec_mulVec, hinv,
        Matrix.one_mulVec, dotProduct_single, mul_one, Pi.star_apply, starRingEnd_apply, star_star]
    have hp : ((star v ⬝ᵥ H *ᵥ Pi.single k 1).im : ℂ) -
        I * ((star v ⬝ᵥ H *ᵥ (I • Pi.single k 1)).im : ℂ) = -I * (star v ⬝ᵥ H *ᵥ Pi.single k 1) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_sub_I_re]
    simp only [Fintype.sum_bool, nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    linear_combination (X k j * (-(1 / (4 * π))) * (l (Pi.single k 1) - I * l (I • Pi.single k 1))) * ha +
      (X k j * (-(1 / (4 * π))) * (l (H⁻¹ *ᵥ Pi.single j 1) + I * l (I • H⁻¹ *ᵥ Pi.single j 1))) * hp
  have hsum : ∀ F : ι × ι × Bool × Bool → ℂ, ∑ i, F i = ∑ k, ∑ j, ∑ b1, ∑ b2, F (k, j, b1, b2) :=
    fun F => by simp only [Fintype.sum_prod_type]
  rw [hsum, Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hkj k j]
  have hsplit : (∑ k, ∑ j, X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
      (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1)))) =
      (-(1 / (4 * π)) * I : ℂ) * ((∑ k, ∑ j, X k j * (v j * linPart l (Pi.single k 1))) -
        ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hLA : linPart l (X *ᵥ v) + antiPart l (X *ᵥ v) = 2 * l (X *ᵥ v) := by
    simp only [linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfin : ∀ z : ℂ, 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = z := by
    intro z
    rw [show 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = -(I * I) * ((π : ℂ) * (π : ℂ)⁻¹) * z by ring,
      I_mul_I, mul_inv_cancel₀ hπ]
    ring
  rw [hsplit, sum_lin, sum_anti hH hd hX, sub_neg_eq_add, hLA]
  exact hfin _

private theorem sm_add' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f g : B} (hf : Sm ρ f) (hg : Sm ρ g) : Sm ρ (f + g) := by
  unfold Sm at *
  simp only [map_add]
  exact hf.add hg

private theorem sm_smul' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f : B} (a : ℂ) (hf : Sm ρ f) : Sm ρ (a • f) := by
  unfold Sm at *
  simp only [map_smul]
  exact hf.const_smul a

theorem quad_normal (H X : Matrix ι ι ℂ) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (f : B) (hs : ∀ v, Sm ρ (dH ρ v f)) :
    quad ρ (nC X) nP (nQ H) f = nOp ρ H X f := by
  have hy : ∀ j : ι, Sm ρ (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _
  have hIy : ∀ j : ι, Sm ρ (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _

  have hexp : ∀ (u : ι → ℂ) (j : ι), dH ρ u (dOp ρ H j f) = (-(1 / (4 * π)) : ℂ) •
      (dH ρ u (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) + I • dH ρ u (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f)) := by
    intro u j
    unfold dOp
    rw [dH_smul u _ (sm_add' (hy j) (sm_smul' I (hIy j))),
      dH_add u (hy j) (sm_smul' I (hIy j)), dH_smul u I (hIy j)]
  unfold quad nOp xOp
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, hexp]
  module

def omH (H : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ι → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun x y : ι → ℂ => (star y ⬝ᵥ H *ᵥ x).im)
        (fun x x' y => by simp [mulVec_add])
        (fun r x y => by simp [mulVec_smul])
        (fun x y y' => by simp)
        (fun r x y => by simp))

theorem normal_quad : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → Xᴴ * H + H * X = 0 → ∃ (κ : Type) (_ : Fintype κ) (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ f, Sm ρ f → quad ρ c p q f = nOp ρ H X f := by
  intro ι _ _ H X hH hd hX
  refine ⟨ι × ι × Bool × Bool, inferInstance, nC X, nP, nQ H, isQuadOf_normal hH hd hX, ?_⟩
  intro B _ _ ρ hρ f hf
  exact quad_normal H X ρ f fun v => DCalc.sm_dH (om := omH H) hρ hf v

end GlobalTheory.Mem.Lift.Normal

end
