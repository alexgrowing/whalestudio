import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceFiniteIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChangeOfNormalisation
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EntireEqZeroOrEqZeroOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MatRmulUnipMulHeadProj
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatDen

open NumberField Matrix Complex
open scoped ComplexConjugate Real
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (thetaChar omegaStd hermForm)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory.CanTh (canTh canMult translConst)

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {g : ℕ}

def latMult (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (a b : Fin g → ℝ) (l : X.Λ) : ℂ :=
  canMult a b (fun i => bas.symm l (Sum.inl i)) (fun i => bas.symm l (Sum.inr i))

def IsMatched (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (a b : Fin g → ℝ)
    (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (a' b' : Fin g → ℝ) : Prop :=
  IsSympl X bas ∧ IsSympl X bas' ∧ ∀ l, latMult X bas a b l = latMult X bas' a' b' l

def chgMat (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  LinearMap.toMatrix' (bas'.trans bas.symm).toLinearMap

def IsSamePt (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (u u' : Fin g ⊕ Fin g → ℝ) : Prop :=
  u = (chgMat X bas bas').map (Int.cast : ℤ → ℝ) *ᵥ u'

variable {X}

theorem chgMat_mulVec (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (m : Fin g ⊕ Fin g → ℤ) :
    chgMat X bas bas' *ᵥ m = bas.symm (bas' m) := by
  rw [chgMat, LinearMap.toMatrix'_mulVec]
  rfl

theorem chgMat_mul_chgMat (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) :
    chgMat X bas bas' * chgMat X bas' bas = 1 := by
  rw [chgMat, chgMat, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  exact LinearMap.ext fun m => by simp

theorem IsSamePt.symm {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {u u' : Fin g ⊕ Fin g → ℝ}
    (h : IsSamePt X bas bas' u u') : IsSamePt X bas' bas u' u := by
  unfold IsSamePt at h ⊢
  have hm := Matrix.map_mul (f := Int.castRingHom ℝ) (L := chgMat X bas' bas) (M := chgMat X bas bas')
  simp only [Int.coe_castRingHom] at hm
  rw [h, Matrix.mulVec_mulVec, ← hm, chgMat_mul_chgMat, Matrix.map_one _ Int.cast_zero Int.cast_one,
    Matrix.one_mulVec]

variable (idx : Fin g ≃ X.Ψ × Fin r)

theorem perCx_chgMat (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (x : Frame X.Ψ r)
    (w : Fin g ⊕ Fin g → ℂ) :
    perCx X bas idx x ((chgMat X bas bas').map (Int.cast : ℤ → ℂ) *ᵥ w) = perCx X bas' idx x w := by
  have key : (perCx X bas idx x).comp ((chgMat X bas bas').map (Int.cast : ℤ → ℂ)).mulVecLin =
      perCx X bas' idx x := by
    refine LinearMap.pi_ext' fun s => LinearMap.ext_ring ?_
    have e : (Pi.single s (1 : ℂ) : Fin g ⊕ Fin g → ℂ) =
        fun t => ((Pi.single s (1 : ℤ) : Fin g ⊕ Fin g → ℤ) t : ℂ) := by
      ext t
      by_cases h : t = s
      · subst h; simp
      · simp [h]
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.mulVecLin_apply, e]
    rw [← GlobalTheory.intCast_mulVec_complex, perCx_int, perCx_int, chgMat_mulVec, LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun key w

theorem IsSamePt.perCx_eq {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {u u' : Fin g ⊕ Fin g → ℝ}
    (h : IsSamePt X bas bas' u u') (x : Frame X.Ψ r) :
    perCx X bas idx x (fun s => (u s : ℂ)) = perCx X bas' idx x (fun s => (u' s : ℂ)) := by
  have hc : (fun s => (u s : ℂ)) = (chgMat X bas bas').map (Int.cast : ℤ → ℂ) *ᵥ fun s => (u' s : ℂ) := by
    rw [show u = _ from h]
    ext s
    simp [Matrix.mulVec, dotProduct]
  rw [hc, perCx_chgMat]

section Laws

variable {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {x : Frame X.Ψ r}

theorem canFn_eq_canTh_mulVec (a b : Fin g → ℝ) (z : Fin g → ℂ) :
    canFn X bas idx a b x z = canTh (tauMat X bas idx x) a b (hMat X bas idx x *ᵥ z) := rfl

theorem hermForm_Hm_indep (hs : IsSympl X bas) (hs' : IsSympl X bas') (hx : x ∈ X.dom)
    (z w : Fin g → ℂ) : hermForm (Hm X bas' idx x) z w = hermForm (Hm X bas idx x) z w := by
  rw [hermForm_Hm_eq_diagonal idx hs' hx z w, hermForm_Hm_eq_diagonal idx hs hx z w]

variable (hs : IsSympl X bas) (hx : x ∈ X.dom)
include hs hx

theorem hMat_mulVec_perCx_real (u : Fin g ⊕ Fin g → ℝ) :
    hMat X bas idx x *ᵥ perCx X bas idx x (fun s => (u s : ℂ)) =
      (fun i => (u (Sum.inl i) : ℂ)) + tauMat X bas idx x *ᵥ fun i => (u (Sum.inr i) : ℂ) := by
  rw [hMat_mulVec_perCx idx hs hx, GlobalTheory.LagSplit.perProj_apply]
  rfl

theorem canFn_entire (a b : Fin g → ℝ) : Differentiable ℂ (canFn X bas idx a b x) := by
  have hf : canFn X bas idx a b x = fun z => canTh (tauMat X bas idx x) a b (hMat X bas idx x *ᵥ z) :=
    funext fun z => canFn_eq_canTh_mulVec idx a b z
  rw [hf]
  exact (GlobalTheory.CanTh.differentiable_canTh (tauMat_im_posDef idx hs hx) a b).comp
    (LinearMap.toContinuousLinearMap (hMat X bas idx x).mulVecLin).differentiable

theorem exists_canFn_ne_zero (a b : Fin g → ℝ) : ∃ z, canFn X bas idx a b x z ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply GlobalTheory.CanTh.canTh_ne_zero (tauMat_isSymm idx hs hx) (tauMat_im_posDef idx hs hx) a b
  funext ζ
  have hz := hc ((hMat X bas idx x)⁻¹ *ᵥ ζ)
  rwa [canFn_eq_canTh_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_det_hMat idx hs hx), Matrix.one_mulVec] at hz

theorem canFn_add_per (a b : Fin g → ℝ) (l : X.Λ) (z : Fin g → ℂ) :
    canFn X bas idx a b x (z + per X x l ∘ idx) = latMult X bas a b l *
      cexp (π * hermForm (Hm X bas idx x) z (per X x l ∘ idx) +
        π / 2 * hermForm (Hm X bas idx x) (per X x l ∘ idx) (per X x l ∘ idx)) *
      canFn X bas idx a b x z := by
  obtain ⟨c, rfl⟩ := bas.surjective l
  have hc : bas c = bas (Sum.elim (fun i => c (Sum.inl i)) (fun i => c (Sum.inr i))) := by
    congr 1
    ext j
    cases j <;> rfl
  have hp : hMat X bas idx x *ᵥ (per X x (bas c) ∘ idx) =
      (fun i => ((c (Sum.inl i) : ℤ) : ℂ)) + tauMat X bas idx x *ᵥ fun i => ((c (Sum.inr i) : ℤ) : ℂ) := by
    rw [hc]
    exact hMat_mulVec_per_bas idx hs hx _ _
  rw [canFn_eq_canTh_mulVec, canFn_eq_canTh_mulVec, Matrix.mulVec_add, hermForm_Hm, hermForm_Hm, hp,
    GlobalTheory.CanTh.canTh_add_period (tauMat_isSymm idx hs hx) (tauMat_im_posDef idx hs hx) a b
      (fun i => c (Sum.inl i)) (fun i => c (Sum.inr i)) rfl]
  simp only [latMult, LinearEquiv.symm_apply_apply]
  rfl

theorem canFn_translate (a b : Fin g → ℝ) (u : Fin g ⊕ Fin g → ℝ) {y : Fin g → ℂ}
    (hy : y = perCx X bas idx x fun s => (u s : ℂ)) (z : Fin g → ℂ) :
    cexp (-(π * hermForm (Hm X bas idx x) z y) - π / 2 * hermForm (Hm X bas idx x) y y) *
        canFn X bas idx a b x (z + y) =
      translConst b (u ∘ Sum.inr) (u ∘ Sum.inl) *
        canFn X bas idx (a + u ∘ Sum.inr) (b + u ∘ Sum.inl) x z := by
  have hy' : hMat X bas idx x *ᵥ y = (fun i => ((u ∘ Sum.inl) i : ℂ)) +
      tauMat X bas idx x *ᵥ fun i => ((u ∘ Sum.inr) i : ℂ) := by
    rw [hy, hMat_mulVec_perCx_real idx hs hx]
    rfl
  rw [canFn_eq_canTh_mulVec, canFn_eq_canTh_mulVec, Matrix.mulVec_add, hermForm_Hm, hermForm_Hm, hy',
    ← GlobalTheory.CanTh.canTh_translate (tauMat_isSymm idx hs hx) (tauMat_im_posDef idx hs hx) a b
      (u ∘ Sum.inr) (u ∘ Sum.inl) rfl]
  rfl

end Laws

section Symplectic

open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

variable (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

def chgSp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  Matrix.fromBlocks (chgMat X bas bas').toBlocks₂₂ᵀ (chgMat X bas bas').toBlocks₁₂ᵀ
    (chgMat X bas bas').toBlocks₂₁ᵀ (chgMat X bas bas').toBlocks₁₁ᵀ

variable {bas bas'} (hs : IsSympl X bas) (hs' : IsSympl X bas')
include hs hs'

theorem chgSp_mem : chgSp bas bas' ∈ Matrix.symplecticGroup (Fin g) ℤ := by
  apply GlobalTheory.PeriodChange.swap_mem_symplectic
  intro a b
  have h1 := hs (bas.symm (bas' a)) (bas.symm (bas' b))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hs' a b] at h1
  have h2 : ((omegaStd (bas.symm (bas' a)) (bas.symm (bas' b)) : ℤ) : ℚ) = (omegaStd a b : ℚ) := by
    linarith
  rw [chgMat_mulVec, chgMat_mulVec]
  exact_mod_cast h2

variable {x : Frame X.Ψ r} (hx : x ∈ X.dom)
include hx

theorem period_chgSp :
    tauMat X bas' idx x = spAct (chgSp bas bas') (tauMat X bas idx x) ∧
    hMat X bas' idx x = ((jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x ∧
    (hMat X bas idx x).det =
      (jAut (chgSp bas bas') (tauMat X bas idx x)).det * (hMat X bas' idx x).det := by
  have hτs := tauMat_isSymm idx hs hx
  have hcol : ∀ s : Fin g → Fin g ⊕ Fin g, perMat X bas' idx s x =
      perMat X bas idx Sum.inl x * Matrix.of (fun j k => ((chgMat X bas bas' (Sum.inl j) (s k) : ℤ) : ℂ)) +
      perMat X bas idx Sum.inr x * Matrix.of (fun j k => ((chgMat X bas bas' (Sum.inr j) (s k) : ℤ) : ℂ)) := by
    intro s
    ext i k
    have e : bas' (Pi.single (s k) 1) = bas (chgMat X bas bas' *ᵥ Pi.single (s k) 1) := by
      rw [chgMat_mulVec, LinearEquiv.apply_symm_apply]
    have hv : ∀ t, (chgMat X bas bas' *ᵥ Pi.single (s k) 1) t = chgMat X bas bas' t (s k) := by
      intro t
      rw [Matrix.mulVec_single_one]
      rfl
    have hp := congrFun (per_bas X bas idx x (chgMat X bas bas' *ᵥ Pi.single (s k) 1)) i
    rw [perMat_apply, e]
    simp only [Function.comp_apply, hv] at hp
    rw [hp]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  set A : Matrix (Fin g) (Fin g) ℂ :=
    Matrix.of (fun j k => ((chgMat X bas bas' (Sum.inl j) (Sum.inl k) : ℤ) : ℂ)) +
      tauMat X bas idx x * Matrix.of (fun j k => ((chgMat X bas bas' (Sum.inr j) (Sum.inl k) : ℤ) : ℂ))
    with hAd
  set B : Matrix (Fin g) (Fin g) ℂ :=
    Matrix.of (fun j k => ((chgMat X bas bas' (Sum.inl j) (Sum.inr k) : ℤ) : ℂ)) +
      tauMat X bas idx x * Matrix.of (fun j k => ((chgMat X bas bas' (Sum.inr j) (Sum.inr k) : ℤ) : ℂ))
    with hBd
  have hA : hMat X bas idx x * perMat X bas' idx Sum.inl x = A := by
    rw [hcol, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMat_mul_perMat idx hs hx,
      Matrix.one_mul]
    rfl
  have hB : hMat X bas idx x * perMat X bas' idx Sum.inr x = B := by
    rw [hcol, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMat_mul_perMat idx hs hx,
      Matrix.one_mul]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.PeriodChange.change_of_normalisation _ _ _ _ _ _ _ hA hB
    (hMat_mul_perMat idx hs' hx) rfl (tauMat_isSymm idx hs' hx) (isUnit_det_hMat idx hs hx)
  have hJ : Aᵀ = jAut (chgSp bas bas') (tauMat X bas idx x) := by
    rw [hAd, Matrix.transpose_add, Matrix.transpose_mul, hτs.eq]
    ext i j
    simp [jAut, ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat, chgSp, Matrix.mul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.transpose_apply]
    ring
  have hN : Bᵀ = (ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat (chgSp bas bas')).toBlocks₁₁ * tauMat X bas idx x +
      (ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat (chgSp bas bas')).toBlocks₁₂ := by
    rw [hBd, Matrix.transpose_add, Matrix.transpose_mul, hτs.eq]
    ext i j
    simp [ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat, chgSp, Matrix.mul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.transpose_apply]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have h1' : tauMat X bas' idx x = Bᵀ * Aᵀ⁻¹ := h1
    rw [h1', hN, hJ]
    rfl
  · rw [h2, hJ]
  · rw [h3, hJ]

theorem dot_imInv_chgSp (z : Fin g → ℂ) :
    (hMat X bas idx x *ᵥ z) ⬝ᵥ imInv X bas idx x *ᵥ (hMat X bas idx x *ᵥ z) =
      (hMat X bas' idx x *ᵥ z) ⬝ᵥ imInv X bas' idx x *ᵥ (hMat X bas' idx x *ᵥ z) +
        2 * I * expArg (chgSp bas bas') (tauMat X bas idx x) (hMat X bas idx x *ᵥ z) := by
  obtain ⟨hτ', hh', -⟩ := period_chgSp idx hs hs' hx
  have hγ := chgSp_mem hs hs'
  have hτs := tauMat_isSymm idx hs hx
  have hτ's := tauMat_isSymm idx hs' hx
  have hS : tauMat X bas idx x ∈ SiegelH (Fin g) := ⟨hτs, tauMat_im_posDef idx hs hx⟩
  have hJu : IsUnit (jAut (chgSp bas bas') (tauMat X bas idx x)).det := jAut_isUnit hγ hS
  have hJHu : IsUnit (jAut (chgSp bas bas') (tauMat X bas idx x))ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hJu.star
  have hI : imInv X bas idx x = (imC (tauMat X bas idx x))⁻¹ :=
    GlobalTheory.CanTh.imInv_eq_inv_map (tauMat_im_posDef idx hs hx)
  have hI' : imInv X bas' idx x = (imC (tauMat X bas' idx x))⁻¹ :=
    GlobalTheory.CanTh.imInv_eq_inv_map (tauMat_im_posDef idx hs' hx)
  have hYY : (imC (tauMat X bas idx x))⁻¹ * imC (tauMat X bas idx x) = 1 := by
    rw [← hI]
    exact GlobalTheory.CanTh.imInv_mul (tauMat_im_posDef idx hs hx)
  have hN : tauMat X bas' idx x * jAut (chgSp bas bas') (tauMat X bas idx x) =
      nAut (chgSp bas bas') (tauMat X bas idx x) := by
    rw [hτ']
    show nAut (chgSp bas bas') (tauMat X bas idx x) * (jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹ *
      jAut (chgSp bas bas') (tauMat X bas idx x) = _
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.mul_one]
  have e1 : (jAut (chgSp bas bas') (tauMat X bas idx x))ᴴ * ((2 * I) • imC (tauMat X bas' idx x)) *
      jAut (chgSp bas bas') (tauMat X bas idx x) = (2 * I) • imC (tauMat X bas idx x) := by
    rw [← sub_conjTranspose_of_symm hτ's, ← sub_conjTranspose_of_symm hτs, ← sp_keyH hγ (tauMat X bas idx x), ← hN,
      Matrix.conjTranspose_mul]
    noncomm_ring
  have e2 : (jAut (chgSp bas bas') (tauMat X bas idx x))ᴴ * imC (tauMat X bas' idx x) *
      jAut (chgSp bas bas') (tauMat X bas idx x) = imC (tauMat X bas idx x) := by
    rw [Matrix.mul_smul, Matrix.smul_mul] at e1
    exact smul_right_injective _ (by simp [Complex.I_ne_zero]) e1
  have hYinv : (imC (tauMat X bas' idx x))⁻¹ = jAut (chgSp bas bas') (tauMat X bas idx x) *
      (imC (tauMat X bas idx x))⁻¹ * (jAut (chgSp bas bas') (tauMat X bas idx x))ᴴ := by
    rw [← e2, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJu,
      Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJHu, Matrix.mul_one]
  have hJH : (jAut (chgSp bas bas') (tauMat X bas idx x))ᴴ = (jAut (chgSp bas bas') (tauMat X bas idx x))ᵀ -
      (2 * I) • (imC (tauMat X bas idx x) * ((cMat (chgSp bas bas')).toBlocks₂₁)ᵀ) := by
    have ht : (tauMat X bas idx x)ᴴ = tauMat X bas idx x - (2 * I) • imC (tauMat X bas idx x) := by
      rw [← sub_conjTranspose_of_symm hτs]
      abel
    simp only [jAut]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, blk_conjTranspose₂₁, blk_conjTranspose₂₂, ht,
      Matrix.transpose_add, Matrix.transpose_mul, hτs.eq, Matrix.sub_mul, Matrix.smul_mul]
    abel
  have hJJ : (imC (tauMat X bas idx x))⁻¹ * (jAut (chgSp bas bas') (tauMat X bas idx x))ᵀ *
      ((jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹)ᵀ = (imC (tauMat X bas idx x))⁻¹ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hJu, Matrix.transpose_one,
      Matrix.mul_one]
  have hM : (imC (tauMat X bas idx x))⁻¹ * (jAut (chgSp bas bas') (tauMat X bas idx x))ᴴ *
      ((jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹)ᵀ = (imC (tauMat X bas idx x))⁻¹ -
      (2 * I) • (((cMat (chgSp bas bas')).toBlocks₂₁)ᵀ * ((jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹)ᵀ) := by
    rw [hJH]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hYY,
      Matrix.one_mul, hJJ]
  have hq : ∀ ζ : Fin g → ℂ, (((jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹)ᵀ *ᵥ ζ) ⬝ᵥ
      (jAut (chgSp bas bas') (tauMat X bas idx x) * (imC (tauMat X bas idx x))⁻¹ *
        (jAut (chgSp bas bas') (tauMat X bas idx x))ᴴ) *ᵥ
        (((jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹)ᵀ *ᵥ ζ) =
      ζ ⬝ᵥ ((imC (tauMat X bas idx x))⁻¹ * (jAut (chgSp bas bas') (tauMat X bas idx x))ᴴ *
        ((jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹)ᵀ) *ᵥ ζ := by
    intro ζ
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    congr 2
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hJu]
  have hE : ∀ ζ : Fin g → ℂ, ζ ⬝ᵥ (((cMat (chgSp bas bas')).toBlocks₂₁)ᵀ *
      ((jAut (chgSp bas bas') (tauMat X bas idx x))⁻¹)ᵀ) *ᵥ ζ =
      expArg (chgSp bas bas') (tauMat X bas idx x) ζ := by
    intro ζ
    rw [← Matrix.transpose_mul, Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    rfl
  have hsm : ∀ (c : ℂ) (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ), (c • M) *ᵥ v = c • (M *ᵥ v) :=
    fun c M v => by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hI, hI', hh', ← Matrix.mulVec_mulVec, hYinv, hq, hM]
  simp only [Matrix.sub_mulVec, hsm, dotProduct_sub, dotProduct_smul, smul_eq_mul, hE]
  ring

omit hx in

theorem exists_sq_law_zero : ∃ (k k' : Fin g → ℤ) (c : ℂ), c ^ 4 = 1 ∧ ∀ x ∈ X.dom, ∀ z,
    (hMat X bas' idx x).det * canFn X bas' idx (halfVec k) (halfVec k') x z ^ 2 =
      c * (hMat X bas idx x).det * canFn X bas idx 0 0 x z ^ 2 := by
  have hγ := chgSp_mem hs hs'
  obtain ⟨k, k', c, -, -, hc4, hlaw⟩ := GlobalTheory.chiStatement_holds g (chgSp bas bas') hγ 0 0
  refine ⟨k, k', c, hc4, fun x hx z => ?_⟩
  obtain ⟨hτ', hh', hdet⟩ := period_chgSp idx hs hs' hx
  have hS : tauMat X bas idx x ∈ SiegelH (Fin g) := ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩
  have hq := dot_imInv_chgSp idx hs hs' hx z
  have h0 : halfVec (0 : Fin g → ℤ) = 0 := by
    funext i
    simp [halfVec]
  have e1 : hMat X bas' idx x *ᵥ z =
      zAct (chgSp bas bas') (tauMat X bas idx x) (hMat X bas idx x *ᵥ z) := by
    rw [hh', ← Matrix.mulVec_mulVec]
    rfl
  have hθ : thetaChar (tauMat X bas' idx x) (fun i => ((halfVec k i : ℝ) : ℂ))
      (fun i => ((halfVec k' i : ℝ) : ℂ)) (hMat X bas' idx x *ᵥ z) ^ 2 =
      c * (jAut (chgSp bas bas') (tauMat X bas idx x)).det *
        eC (expArg (chgSp bas bas') (tauMat X bas idx x) (hMat X bas idx x *ᵥ z)) *
        thetaChar (tauMat X bas idx x) (fun i => (((0 : Fin g → ℝ) i : ℝ) : ℂ))
          (fun i => (((0 : Fin g → ℝ) i : ℝ) : ℂ)) (hMat X bas idx x *ᵥ z) ^ 2 := by
    rw [GlobalTheory.CanTh.thetaChar_eq_theta, GlobalTheory.CanTh.thetaChar_eq_theta, e1, hτ',
      hlaw _ hS (hMat X bas idx x *ᵥ z), h0]
  have hexp : cexp (Real.pi / 2 * ((hMat X bas idx x *ᵥ z) ⬝ᵥ imInv X bas idx x *ᵥ (hMat X bas idx x *ᵥ z))) ^ 2 =
      cexp (Real.pi / 2 * ((hMat X bas' idx x *ᵥ z) ⬝ᵥ imInv X bas' idx x *ᵥ (hMat X bas' idx x *ᵥ z))) ^ 2 *
        eC (expArg (chgSp bas bas') (tauMat X bas idx x) (hMat X bas idx x *ᵥ z)) := by
    rw [hq, eC, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold canFn
  rw [mul_pow, mul_pow, hθ, hexp, hdet]
  ring

end Symplectic

theorem exists_int_of_canMult_eq {a b a' b' : Fin g → ℝ}
    (h : ∀ m n, canMult a b m n = canMult a' b' m n) :
    ∃ n m : Fin g → ℤ, a' = a + (fun i => (n i : ℝ)) ∧ b' = b + fun i => (m i : ℝ) := by
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hd : ∀ (c : Fin g → ℝ) (i : Fin g), (c ⬝ᵥ fun j => ((Pi.single i (1 : ℤ) : Fin g → ℤ) j : ℝ)) = c i := by
    intro c i
    simp [dotProduct, Pi.single_apply]
  have hz : ∀ c : Fin g → ℝ, (c ⬝ᵥ fun _ => (0 : ℝ)) = 0 := fun c => by simp [dotProduct]
  have ha : ∀ i, ∃ k : ℤ, a' i = a i + k := by
    intro i
    have e := h (Pi.single i 1) 0
    simp only [canMult, hd, hz, dotProduct_zero, Pi.zero_apply, Int.cast_zero, Complex.ofReal_zero] at e
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
    refine ⟨-k, ?_⟩
    have h2 : ((a' i : ℝ) : ℂ) * (2 * π * I) = ((a i + ((-k : ℤ) : ℝ) : ℝ) : ℂ) * (2 * π * I) := by
      push_cast
      linear_combination -hk
    exact_mod_cast mul_right_cancel₀ hπ h2
  have hb : ∀ i, ∃ k : ℤ, b' i = b i + k := by
    intro i
    have e := h 0 (Pi.single i 1)
    simp only [canMult, hd, hz, zero_dotProduct, Pi.zero_apply, Int.cast_zero, Complex.ofReal_zero] at e
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
    refine ⟨k, ?_⟩
    have h2 : ((b' i : ℝ) : ℂ) * (2 * π * I) = ((b i + ((k : ℤ) : ℝ) : ℝ) : ℂ) * (2 * π * I) := by
      push_cast
      linear_combination hk
    exact_mod_cast mul_right_cancel₀ hπ h2
  choose n hn using ha
  choose m hm using hb
  exact ⟨n, m, funext hn, funext hm⟩

variable (X) in

def IsProportional (κ : ℂ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (a b : Fin g → ℝ)
    (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (a' b' : Fin g → ℝ) : Prop :=
  ∀ x ∈ X.dom, ∃ μ : ℂ, μ ^ 2 * (hMat X bas' idx x).det = κ * (hMat X bas idx x).det ∧
    ∀ z, canFn X bas' idx a' b' x z = μ * canFn X bas idx a b x z

section Proportional

variable {idx} {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {κ : ℂ} {a b a' b' : Fin g → ℝ}

theorem IsProportional.add_int (h : IsProportional X idx κ bas a b bas' a' b') (n m : Fin g → ℤ) :
    IsProportional X idx (κ * cexp (2 * π * I * ((a' ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ)) ^ 2) bas a b
      bas' (a' + fun i => (n i : ℝ)) (b' + fun i => (m i : ℝ)) := by
  intro x hx
  obtain ⟨μ, hμ, hf⟩ := h x hx
  refine ⟨cexp (2 * π * I * ((a' ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ)) * μ, ?_, fun z => ?_⟩
  · linear_combination (cexp (2 * π * I * ((a' ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ))) ^ 2 * hμ
  · rw [canFn_eq_canTh_mulVec, GlobalTheory.CanTh.canTh_add_int, ← canFn_eq_canTh_mulVec, hf z]
    ring

variable (hs : IsSympl X bas) (hs' : IsSympl X bas')
include hs hs'

theorem isProportional_of_sq_law (h : ∀ x ∈ X.dom, ∀ z,
    (hMat X bas' idx x).det * canFn X bas' idx a' b' x z ^ 2 =
      κ * (hMat X bas idx x).det * canFn X bas idx a b x z ^ 2) :
    IsProportional X idx κ bas a b bas' a' b' := by
  intro x hx
  have hd' := (isUnit_det_hMat idx hs' hx).ne_zero
  obtain ⟨c, hc, hf⟩ := GlobalTheory.entire_eq_mul_of_sq_eq_mul_sq g (canFn X bas' idx a' b' x)
    (canFn X bas idx a b x) (fun _ => 0) (κ * (hMat X bas idx x).det / (hMat X bas' idx x).det)
    (canFn_entire idx hs' hx a' b') (canFn_entire idx hs hx a b) (differentiable_const 0)
    (fun z => by
      simp only [mul_zero, Complex.exp_zero, mul_one]
      field_simp
      linear_combination h x hx z)
  refine ⟨c, ?_, fun z => ?_⟩
  · rw [hc]
    field_simp
  · rw [hf z]
    simp

theorem canFn_translate_eq_mul {x : Frame X.Ψ r} (hx : x ∈ X.dom) {μ : ℂ}
    (h : ∀ z, canFn X bas' idx a' b' x z = μ * canFn X bas idx a b x z)
    {u u' : Fin g ⊕ Fin g → ℝ} (hu : IsSamePt X bas bas' u u') (z : Fin g → ℂ) :
    canFn X bas' idx (a' + u' ∘ Sum.inr) (b' + u' ∘ Sum.inl) x z =
      translConst b (u ∘ Sum.inr) (u ∘ Sum.inl) / translConst b' (u' ∘ Sum.inr) (u' ∘ Sum.inl) * μ *
        canFn X bas idx (a + u ∘ Sum.inr) (b + u ∘ Sum.inl) x z := by
  have hy : perCx X bas idx x (fun s => (u s : ℂ)) = perCx X bas' idx x (fun s => (u' s : ℂ)) :=
    hu.perCx_eq idx x
  have e1 := canFn_translate idx hs hx a b u rfl z
  have e2 := canFn_translate idx hs' hx a' b' u' hy z
  rw [hermForm_Hm_indep idx hs hs' hx, hermForm_Hm_indep idx hs hs' hx, h] at e2
  have ht : translConst b' (u' ∘ Sum.inr) (u' ∘ Sum.inl) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  linear_combination μ * e1 - e2

theorem IsProportional.translate (h : IsProportional X idx κ bas a b bas' a' b')
    {u u' : Fin g ⊕ Fin g → ℝ} (hu : IsSamePt X bas bas' u u') :
    IsProportional X idx (κ * (translConst b (u ∘ Sum.inr) (u ∘ Sum.inl) /
      translConst b' (u' ∘ Sum.inr) (u' ∘ Sum.inl)) ^ 2) bas (a + u ∘ Sum.inr) (b + u ∘ Sum.inl)
      bas' (a' + u' ∘ Sum.inr) (b' + u' ∘ Sum.inl) := by
  intro x hx
  obtain ⟨μ, hμ, hf⟩ := h x hx
  refine ⟨translConst b (u ∘ Sum.inr) (u ∘ Sum.inl) / translConst b' (u' ∘ Sum.inr) (u' ∘ Sum.inl) * μ,
    ?_, fun z => canFn_translate_eq_mul hs hs' hx hf hu z⟩
  linear_combination (translConst b (u ∘ Sum.inr) (u ∘ Sum.inl) /
    translConst b' (u' ∘ Sum.inr) (u' ∘ Sum.inl)) ^ 2 * hμ

private theorem chartRestrictionData_dom_nonempty : X.dom.Nonempty := by
  choose P hP hG using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have hd : dmin X.Gm (fun τ => P τ) τ i = ∏ j : Fin i, ((sgn X.p0 j : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show mat (fun τ => P τ) τ = P τ from rfl, hG τ,
      show Fin.castLE (Nat.le_of_lt_succ i.isLt) = ⇑(Fin.castLEEmb (Nat.le_of_lt_succ i.isLt)) from rfl,
      Matrix.submatrix_diagonal_embedding, Matrix.det_diagonal]
    rfl
  have h1 : ∀ a, sgn X.p0 a * sgn X.p0 a = 1 := fun a => by
    unfold sgn
    split_ifs <;> norm_num
  rw [hd, ← Complex.ofReal_prod, Complex.ofReal_re, Fin.prod_univ_eq_prod_range (fun j => sgn X.p0 j), psgn,
    ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun a _ => h1 a), Finset.prod_const_one]
  exact one_pos

theorem IsProportional.isMatched (h : IsProportional X idx κ bas a b bas' a' b') :
    IsMatched X bas a b bas' a' b' := by
  refine ⟨hs, hs', fun l => ?_⟩
  obtain ⟨x, hx⟩ := chartRestrictionData_dom_nonempty hs hs'
  obtain ⟨μ, -, hf⟩ := h x hx
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw⟩ := exists_canFn_ne_zero idx hs' hx a' b'
    exact hw (by rw [hf w, zero_mul])
  obtain ⟨z, hz⟩ := exists_canFn_ne_zero idx hs hx a b
  have e1 := canFn_add_per idx hs hx a b l z
  have e2 := canFn_add_per idx hs' hx a' b' l z
  rw [hf, hf, hermForm_Hm_indep idx hs hs' hx, hermForm_Hm_indep idx hs hs' hx, e1] at e2
  have key : ∀ {L1 L2 E F : ℂ}, μ * (L1 * E * F) = L2 * E * (μ * F) → E ≠ 0 → F ≠ 0 → L1 = L2 := by
    intro L1 L2 E F he hE hF
    have h0 : (L1 - L2) * (μ * E * F) = 0 := by linear_combination he
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 (mul_ne_zero (mul_ne_zero hμ0 hE) hF)
  exact key e2 (Complex.exp_ne_zero _) hz

variable (idx) in

theorem exists_isProportional : ∃ k k' : Fin g → ℤ, ∀ u u' : Fin g ⊕ Fin g → ℝ,
    IsSamePt X bas bas' u u' → ∃ κ : ℂ, ‖κ‖ = 1 ∧ IsProportional X idx κ bas (u ∘ Sum.inr)
      (u ∘ Sum.inl) bas' ((fun i => (k i : ℝ) / 2) + u' ∘ Sum.inr)
        ((fun i => (k' i : ℝ) / 2) + u' ∘ Sum.inl) := by
  obtain ⟨k, k', c, hc4, hsq⟩ := exists_sq_law_zero idx hs hs'
  refine ⟨k, k', fun u u' hu => ?_⟩
  have hp0 : IsProportional X idx c bas 0 0 bas' (ReciprocityTheory.ChartRestriction.G.Key.halfVec k) (ReciprocityTheory.ChartRestriction.G.Key.halfVec k') :=
    isProportional_of_sq_law hs hs' hsq
  have hpt := hp0.translate hs hs' hu
  rw [zero_add, zero_add] at hpt
  have hcn : ‖c‖ = 1 := by
    have h4 : ‖c‖ ^ 4 = 1 := by rw [← norm_pow, hc4, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by norm_num)).1 h4
  refine ⟨_, ?_, hpt⟩
  rw [norm_mul, norm_pow, norm_div, GlobalTheory.CanTh.norm_translConst, GlobalTheory.CanTh.norm_translConst, hcn]
  norm_num

omit hs hs' in
variable (idx) in

theorem IsMatched.exists_isProportional (h : IsMatched X bas a b bas' a' b') :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ IsProportional X idx κ bas a b bas' a' b' := by
  obtain ⟨hs, hs', hl⟩ := h
  obtain ⟨k, k', hk⟩ := GlobalTheory.ThFr.exists_isProportional idx hs hs'
  have hu : IsSamePt X bas bas' (Sum.elim b a)
      ((chgMat X bas' bas).map (Int.cast : ℤ → ℝ) *ᵥ Sum.elim b a) := IsSamePt.symm rfl
  obtain ⟨κ, hκ, hp⟩ := hk _ _ hu
  have hm := (hp.isMatched hs hs').2.2
  have hcm : ∀ m n, canMult ((fun i => (k i : ℝ) / 2) +
        ((chgMat X bas' bas).map (Int.cast : ℤ → ℝ) *ᵥ Sum.elim b a) ∘ Sum.inr)
      ((fun i => (k' i : ℝ) / 2) + ((chgMat X bas' bas).map (Int.cast : ℤ → ℝ) *ᵥ Sum.elim b a) ∘ Sum.inl)
      m n = canMult a' b' m n := by
    intro m n
    have e := (hm (bas' (Sum.elim m n))).symm.trans (hl (bas' (Sum.elim m n)))
    simpa only [latMult, LinearEquiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using e
  obtain ⟨n, m, hn, hm'⟩ := exists_int_of_canMult_eq hcm
  have hq := hp.add_int n m
  rw [hn, hm']
  refine ⟨_, ?_, hq⟩
  rw [norm_mul, norm_pow, hκ, Complex.norm_exp]
  simp

end Proportional

end

end GlobalTheory.ThFr
