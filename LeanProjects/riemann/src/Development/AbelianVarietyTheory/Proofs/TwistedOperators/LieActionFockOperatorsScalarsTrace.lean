import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignaturesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtPhiCol

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.LieFock

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LieScalar

theorem signBlockDeterminant_one {n : ℕ} (ε : Fin n → Bool) (e : Bool) : signBlockDeterminant ε e 1 = 1 := by
  unfold signBlockDeterminant
  rw [Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

theorem hasDerivAt_signBlockDeterminant_exp_smul {n : ℕ} (ε : Fin n → Bool) (e : Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => signBlockDeterminant ε e (NormedSpace.exp (t • Y))) (∑ j, if ε j = e then Y j j else 0) 0 := by
  have h := GlobalTheory.HolDS.DerPt.hasDerivAt_det_of_one
    (fun t : ℝ => (NormedSpace.exp (t • Y)).submatrix (Subtype.val : {a // ε a = e} → Fin n) Subtype.val)
    (Y.submatrix Subtype.val Subtype.val)
    (by simp only [zero_smul, NormedSpace.exp_zero]; exact Matrix.submatrix_one _ Subtype.val_injective)
    (fun i j => GlobalTheory.HolDS.DerPt.hasDerivAt_exp_entry Y i.1 j.1)
  have e2 : (Y.submatrix (Subtype.val : {a // ε a = e} → Fin n) Subtype.val).trace =
      ∑ j, if ε j = e then Y j j else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter fun a => ε a = e) (fun a => by simp) (fun a => Y a a)).symm
  rw [e2] at h
  exact h

theorem hasDerivAt_dfac {n : ℕ} (ε : Fin n → Bool) (x : Bool → ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => signBlockDeterminant ε true (NormedSpace.exp (t • Y)) ^ x true *
        signBlockDeterminant ε false (NormedSpace.exp (t • Y)) ^ x false) (∑ j, Y j j * (x (ε j) : ℂ)) 0 := by
  have e0 : ∀ e, signBlockDeterminant ε e (NormedSpace.exp ((0 : ℝ) • Y)) = 1 := fun e => by
    rw [zero_smul, NormedSpace.exp_zero, signBlockDeterminant_one]
  have hz : ∀ (m : ℤ) (e : Bool), HasDerivAt (fun t : ℝ => signBlockDeterminant ε e (NormedSpace.exp (t • Y)) ^ m)
      ((m : ℂ) * ∑ j, if ε j = e then Y j j else 0) 0 := fun m e => by
    have h0 := hasDerivAt_zpow m (signBlockDeterminant ε e (NormedSpace.exp ((0 : ℝ) • Y))) (Or.inl (by rw [e0]; exact one_ne_zero))
    have h1 := h0.comp (0 : ℝ) (hasDerivAt_signBlockDeterminant_exp_smul ε e Y)
    rw [e0, _root_.one_zpow, mul_one] at h1
    exact h1
  refine ((hz (x true) true).fun_mul (hz (x false) false)).congr_deriv ?_
  simp only [e0, _root_.one_zpow, mul_one, one_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases ε j <;> simp <;> ring
section Poly

variable {D : D7}

variable {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

local notation "cc" => MvPolynomial.constantCoeff

theorem sgn_sq (e : Bool) : sgn e * sgn e = 1 := by cases e <;> simp [sgn]

theorem cc_rai_low (i i' : Fin b) (j j' : Fin a) :
    cc ((raiO τ ε ε' i j * lowO τ ε ε' i' j') (1 : PolF D b a)) =
      if i = i' ∧ j = j' ∧ ε' i ≠ ε j then -1 else 0 := by
  classical
  by_cases h1 : ε' i' = ε j'
  · have e : lowO τ ε ε' i' j' (1 : PolF D b a) = 0 := by
      simp [lowO, h1]
    rw [Module.End.mul_apply, e, map_zero, map_zero, if_neg]
    rintro ⟨rfl, rfl, h⟩
    exact h h1
  · have e : lowO τ ε ε' i' j' (1 : PolF D b a) = sgn (ε j') • MvPolynomial.X (τ, i', j') := by
      simp [lowO, h1]
    rw [Module.End.mul_apply, e, LinearMap.map_smul]
    by_cases h2 : ε' i = ε j
    · have h3 : ¬ (i = i' ∧ j = j' ∧ ε' i ≠ ε j) := fun h => h.2.2 h2
      rw [if_neg h3]
      simp [raiO, h2, MvPolynomial.smul_eq_C_mul]
    · by_cases h3 : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := h3
        simp [raiO, h2, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_X_self, sgn_sq]
      · have : (τ, i, j) ≠ (τ, i', j') := fun h => h3 (by simpa using h)
        simp [raiO, h2, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_X_of_ne this.symm]
        tauto

theorem sum_half (e : Bool) {m : ℕ} (ε₁ : Fin m → Bool) :
    (∑ i, ((if ε₁ i ≠ e then (-1 : ℂ) else 0) + 1 / 2)) = sgn e * (idx ε₁ : ℂ) / 2 := by
  unfold idx
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases e <;> cases ε₁ i <;> simp [sgn] <;> norm_num

theorem cc_fockS (Y : Matrix (Fin a) (Fin a) ℂ) :
    cc (fockS τ ε ε' Y (1 : PolF D b a)) = ∑ j, Y j j * (sgn (ε j) * (idx ε' : ℂ) / 2) := by
  classical
  unfold fockS
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.constantCoeff_C, ← sum_half]
    simp only [LinearMap.sum_apply, LinearMap.add_apply, map_sum, map_add, cc_rai_low, if_true]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [MvPolynomial.smul_eq_C_mul]
  · intro k _ hk
    rw [MvPolynomial.smul_eq_C_mul, map_mul]
    simp only [LinearMap.sum_apply, LinearMap.add_apply, map_sum, map_add, cc_rai_low]
    simp [Ne.symm hk]
  · simp

theorem cc_fockT (Y : Matrix (Fin b) (Fin b) ℂ) :
    cc (fockT τ ε ε' Y (1 : PolF D b a)) = ∑ i, Y i i * (sgn (ε' i) * (idx ε : ℂ) / 2) := by
  classical
  unfold fockT
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.constantCoeff_C, ← sum_half]
    simp only [LinearMap.sum_apply, LinearMap.add_apply, map_sum, map_add, cc_rai_low, if_true]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [MvPolynomial.smul_eq_C_mul, ne_comm, eq_comm]
  · intro k _ hk
    rw [MvPolynomial.smul_eq_C_mul, map_mul]
    simp only [LinearMap.sum_apply, LinearMap.add_apply, map_sum, map_add, cc_rai_low]
    simp [Ne.symm hk]
  · simp

theorem cc_subst (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) (R : PolF D b a) :
    cc (subst τ ε ε' g k R) = cc R := by
  classical
  induction R using MvPolynomial.induction_on with
  | C r => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.constantCoeff_X]
    have : cc (subst τ ε ε' g k (MvPolynomial.X v)) = 0 := by
      simp only [subst, MvPolynomial.aeval_X]
      split_ifs <;> simp [MvPolynomial.smul_eq_C_mul]
    rw [this]

end Poly
section Frame

variable {n : ℕ} {F G X : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool}

theorem exp_conj_self {J B B' : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (h : J * B * J = B') :
    J * NormedSpace.exp B = NormedSpace.exp B' * J := by
  have u : IsUnit J := ⟨⟨J, J, hJ, hJ⟩, rfl⟩
  have e := Matrix.exp_conj J B u
  rw [Matrix.inv_eq_right_inv hJ, h] at e
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, hJ, Matrix.mul_one]

def cartM (F : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ := F⁻¹ * Formalism.REAL.Jm ε * F

theorem fr_cart (hF : IsUnit F.det) : F * cartM F ε = Formalism.REAL.Jm ε * F := by
  rw [cartM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF, Matrix.one_mul]

theorem cart_inv (hF : IsUnit F.det) : cartM F ε * F⁻¹ = F⁻¹ * Formalism.REAL.Jm ε := by
  rw [cartM, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF, Matrix.mul_one]

theorem cart_sq (hF : IsUnit F.det) : cartM F ε * cartM F ε = 1 := by
  unfold cartM
  calc _ = F⁻¹ * Formalism.REAL.Jm ε * (F * F⁻¹) * Formalism.REAL.Jm ε * F := by simp only [Matrix.mul_assoc]
    _ = F⁻¹ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * F := by
      rw [Matrix.mul_nonsing_inv _ hF, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Jm_mul_self, Matrix.mul_one, Matrix.nonsing_inv_mul _ hF]

theorem cart_gram (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) : (cartM F ε)ᴴ * G = G * cartM F ε := by
  have h1 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hF, conjTranspose_one]
  rw [← hG, cartM, conjTranspose_mul, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose]
  have L : Fᴴ * (Formalism.REAL.Jm ε * (F⁻¹)ᴴ) * (Fᴴ * Formalism.REAL.Jm ε * F) = Fᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * F := by
    calc _ = Fᴴ * Formalism.REAL.Jm ε * ((F⁻¹)ᴴ * Fᴴ) * Formalism.REAL.Jm ε * F := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h1, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
  have R : Fᴴ * Formalism.REAL.Jm ε * F * (F⁻¹ * Formalism.REAL.Jm ε * F) = Fᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * F := by
    calc _ = Fᴴ * Formalism.REAL.Jm ε * (F * F⁻¹) * Formalism.REAL.Jm ε * F := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.mul_nonsing_inv _ hF, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
  rw [L, R]

theorem cart_mem_UH (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) :
    (cartM F ε)ᴴ * G * cartM F ε = G := by
  rw [cart_gram hF hG, Matrix.mul_assoc, cart_sq hF, Matrix.mul_one]

theorem cart_lie (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) (hX : Xᴴ * G + G * X = 0) :
    (cartM F ε * X * cartM F ε)ᴴ * G + G * (cartM F ε * X * cartM F ε) = 0 := by
  have h := cart_gram hF hG
  set J := cartM F ε
  calc _ = Jᴴ * Xᴴ * (Jᴴ * G) + (G * J) * X * J := by
        rw [conjTranspose_mul, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Jᴴ * Xᴴ * (G * J) + (Jᴴ * G) * X * J := by rw [h]
    _ = Jᴴ * (Xᴴ * G + G * X) * J := by
        simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]

theorem half_lie {c : ℂ} (hc : starRingEnd ℂ c = c) (hX : Xᴴ * G + G * X = 0) : (c • X)ᴴ * G + G * (c • X) = 0 := by
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, hc, ← smul_add, hX, smul_zero]

def partK (F : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (X + cartM F ε * X * cartM F ε)

def partP (F : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (X - cartM F ε * X * cartM F ε)

theorem part_add : partK F ε X + partP F ε X = X := by
  unfold partK partP
  rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ X, smul_smul]
  norm_num

theorem half_conj : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
  have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.conj_ofReal]

theorem partK_lie (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) (hX : Xᴴ * G + G * X = 0) :
    (partK F ε X)ᴴ * G + G * partK F ε X = 0 := by
  refine half_lie half_conj ?_
  have h := cart_lie hF hG hX
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, h, add_zero]

theorem partP_lie (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) (hX : Xᴴ * G + G * X = 0) :
    (partP F ε X)ᴴ * G + G * partP F ε X = 0 := by
  refine half_lie half_conj ?_
  have h := cart_lie hF hG hX
  rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hX, h, sub_zero]

theorem partP_anti (hF : IsUnit F.det) : cartM F ε * partP F ε X * cartM F ε = -partP F ε X := by
  have h := cart_sq (ε := ε) hF
  have e : cartM F ε * (cartM F ε * X * cartM F ε) * cartM F ε = X := by
    calc _ = (cartM F ε * cartM F ε) * X * (cartM F ε * cartM F ε) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h, Matrix.one_mul, Matrix.mul_one]
  unfold partP
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, e, ← smul_neg, neg_sub]

theorem fr_conj (hF : IsUnit F.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    F * (cartM F ε * Z * cartM F ε) * F⁻¹ = Formalism.REAL.Jm ε * (F * Z * F⁻¹) * Formalism.REAL.Jm ε := by
  calc _ = (F * cartM F ε) * Z * (cartM F ε * F⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [fr_cart hF, cart_inv hF]; simp only [Matrix.mul_assoc]

theorem partK_entry (hF : IsUnit F.det) (j k : Fin n) : (F * partK F ε X * F⁻¹) j k =
    (1 / 2 : ℂ) * (1 + sgn (ε j) * sgn (ε k)) * (F * X * F⁻¹) j k := by
  unfold partK
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, fr_conj hF, Matrix.smul_apply, Matrix.add_apply,
    Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  ring

theorem partK_block (hF : IsUnit F.det) {j k : Fin n} (h : ε j ≠ ε k) : (F * partK F ε X * F⁻¹) j k = 0 := by
  rw [partK_entry hF, sgn_mul, if_neg h]
  simp

theorem partK_diag (hF : IsUnit F.det) (j : Fin n) : (F * partK F ε X * F⁻¹) j j = (F * X * F⁻¹) j j := by
  rw [partK_entry hF, sgn_mul_self]
  ring

theorem partK_skew (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) (hX : Xᴴ * G + G * X = 0) :
    (F * partK F ε X * F⁻¹)ᴴ = -(F * partK F ε X * F⁻¹) := by
  ext j k
  rw [conjTranspose_apply, Complex.star_def, lie_entry hF hG (partK_lie hF hG hX), Matrix.neg_apply]
  by_cases h : ε j = ε k
  · rw [sgn_mul, if_pos h.symm]
    ring
  · rw [partK_block hF h]
    simp

theorem partK_comm (hF : IsUnit F.det) :
    (F * partK F ε X * F⁻¹) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (F * partK F ε X * F⁻¹) := by
  ext j k
  rw [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε j = ε k
  · rw [h, mul_comm]
  · rw [partK_block hF h]
    simp

theorem exp_mem_K (hF : IsUnit F.det) (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) (hX : Xᴴ * G + G * X = 0) (t : ℝ) :
    NormedSpace.exp (t • (F * partK F ε X * F⁻¹)) ∈ Formalism.REAL.Kset ε := by
  set Y := F * partK F ε X * F⁻¹
  have h1 : (t • Y)ᴴ = -(t • Y) := by
    rw [conjTranspose_smul, star_trivial, partK_skew hF hG hX, smul_neg]
  have hJ := Jm_mul_self ε
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, h1,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Y)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  · refine (exp_conj_self hJ ?_).symm
    have e : Formalism.REAL.Jm ε * Y * Formalism.REAL.Jm ε = Y := by
      rw [← partK_comm hF, Matrix.mul_assoc, hJ, Matrix.mul_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, e]

theorem exp_frame (hF : IsUnit F.det) (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    F⁻¹ * NormedSpace.exp (t • (F * Z * F⁻¹)) * F = NormedSpace.exp (t • Z) := by
  have u : IsUnit F := (Matrix.isUnit_iff_isUnit_det _).2 hF
  rw [← Matrix.exp_conj' F _ u]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hF, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hF, Matrix.one_mul]

end Frame
section Group

open scoped Classical

variable {D : D7}

local notation "cc" => MvPolynomial.constantCoeff

theorem der_add {θ : InfFam D} (hθ : IsInfFam θ) {U : HSp D} (𝒮 : Set (GA D U → ℂ)) (hc : ∀ φ ∈ 𝒮, Continuous φ)
    (hd : ∀ φ ∈ 𝒮, ∀ τ, ∀ X ∈ lieAt U τ, ∃ φ' ∈ 𝒮, ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ U τ X t)) (φ' g) 0)
    {φ : GA D U → ℂ} (hφ : φ ∈ 𝒮) {τ : D.what₂.Tau} {X Y : Matrix (Fin U.rank) (Fin U.rank) ℂ}
    (hX : X ∈ lieAt U τ) (hY : Y ∈ lieAt U τ) (hXY : X + Y ∈ lieAt U τ) {a b c : ℂ}
    (ha : HasDerivAt (fun t : ℝ => φ (oneP θ U τ X t)) a 0)
    (hb : HasDerivAt (fun t : ℝ => φ (oneP θ U τ Y t)) b 0)
    (hc' : HasDerivAt (fun t : ℝ => φ (oneP θ U τ (X + Y) t)) c 0) : c = a + b := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ U
  have h1 := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ U 𝒮 hc hd φ hφ
  have h2 : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ U) φ :=
    (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 h1)
  have h3 := ((h2 1).differentiable (by simp) 0).hasFDerivAt
  have key : ∀ (Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt U τ) {d : ℂ}, HasDerivAt (fun t : ℝ => φ (oneP θ U τ Z.1 t)) d 0 →
      d = fderiv ℝ (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X)) 0
        (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ Z) := by
    intro Z d hd'
    have h4 : ∀ v : GlobalTheory.SmoothForms.LieN U, HasDerivAt (fun t : ℝ => t • v) v 0 := fun v => by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const v
      rwa [one_smul] at h
    have h3' : HasFDerivAt (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X))
        (fderiv ℝ (fun X : GlobalTheory.SmoothForms.LieN U => φ (1 * GlobalTheory.SmoothForms.expInf θ U X)) 0)
        ((0 : ℝ) • (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ Z : GlobalTheory.SmoothForms.LieN U)) := by
      rw [zero_smul]
      exact h3
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h3' (h4 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ Z))
    refine hd'.unique (h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    simp only [Function.comp, one_mul]
    exact congrArg φ (GlobalTheory.SmoothForms.oneP_eq R τ Z t)
  have eA := key ⟨X, hX⟩ ha
  have eB := key ⟨Y, hY⟩ hb
  have eC := key ⟨X + Y, hXY⟩ hc'
  have e : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ ⟨X + Y, hXY⟩ =
      GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ ⟨X, hX⟩ + GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace U τ ⟨Y, hY⟩ := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace
    rw [← Pi.single_add]
    rfl
  rw [eA, eB, eC, e]
  exact map_add _ _ _

variable {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem gen_path (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (γ : ℝ → GA D V × GA D W) (h1 : Continuous γ)
    (h2 : ∀ s t, γ (s + t) = γ s * γ t) (h3 : ∀ t, (γ t).1 ∈ GinfC V ∧ (γ t).2 ∈ GinfC W)
    (X : Matrix (Ix V W) (Ix V W) ℂ) (h4 : ∀ k l, HasDerivAt (fun t => mM θ V W (γ t) k l) (X k l) 0)
    (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) :
    ∃ G, IsThetaFunO ψ V W G ∧ ∀ p z, HasDerivAt (fun t : ℝ => ω (p * γ t) f z) (ω p G z) 0 := by
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl⟩ := GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ V W ω (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
    γ h1 h2 h3 X h4
  have e := coe_toB hψ f hf
  have hF : IsThetaFunO ψ V W (toB hψ f hf).1 := e.symm ▸ hf
  obtain ⟨x, d, -, hxd⟩ := GlobalTheory.T.exists_ccr_operators_thetaFunctions D θ σ h ψ hψ V W
  have hA : IsThetaFunO ψ V W (nOp (rhoV hψ σ V W) (HM V W) X (toB hψ f hf) + lam • toB hψ f hf).1 := by
    have h5 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨(toB hψ f hf).1, hF⟩).2
    rw [hxd X ⟨(toB hψ f hf).1, hF⟩ (toB hψ f hf) rfl] at h5
    exact (thetaSub ψ V W).add_mem h5 ((thetaSub ψ V W).smul_mem lam hF)
  refine ⟨_, hA, fun p z => ?_⟩
  have h6 := hl (toB hψ f hf) hF p z
  rwa [e] at h6

theorem genS (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) :
    ∃ G, IsThetaFunO ψ V W G ∧ ∀ p z, HasDerivAt (fun t : ℝ =>
      ω (p * MonoidHom.inl (GA D V) (GA D W) (oneP θ V τ X t)) f z) (ω p G z) 0 :=
  gen_path hθ hω (fun t => (oneP θ V τ X t, 1)) ((continuous_oneP hθ hX).prodMk continuous_const)
    (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-X))) (fun k l => by
      simp only [mM_apply, WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
        WeylAction.blk_apply]
      split_ifs
      · exact (WeylAction.hasDerivAt_comp hθ (WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
      · exact hasDerivAt_const _ _) f hf

theorem genT (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (τ : D.what₂.Tau)
    (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hY : Y ∈ lieAt W τ) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) :
    ∃ G, IsThetaFunO ψ V W G ∧ ∀ p z, HasDerivAt (fun t : ℝ =>
      ω (p * MonoidHom.inr (GA D V) (GA D W) (oneP θ W τ Y t)) f z) (ω p G z) 0 :=
  gen_path hθ hω (fun t => (1, oneP θ W τ Y t)) (continuous_const.prodMk (continuous_oneP hθ hY))
    (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) (blk (Pi.single τ Y) fun _ => 1) (fun k l => by
      simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]
      split_ifs
      · exact (WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
      · exact hasDerivAt_const _ _) f hf

end Group

section Core

open scoped Classical

variable {D : D7} {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

local notation "cc" => MvPolynomial.constantCoeff

theorem cc_smul_one {ι' : Type} (c : ℂ) : cc (c • (1 : MvPolynomial ι' ℂ)) = c := by
  simp [MvPolynomial.smul_eq_C_mul]

theorem real_lie {n : ℕ} {G X : Matrix (Fin n) (Fin n) ℂ} (t : ℝ) (hX : Xᴴ * G + G * X = 0) :
    (t • X)ᴴ * G + G * (t • X) = 0 := by
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem Jm_mem_K {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε ∈ Formalism.REAL.Kset ε := by
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, rfl⟩
  rw [Matrix.star_eq_conjTranspose, Formalism.REAL.Jm_conjTranspose, Jm_mul_self]

theorem kappa_core {U : HSp D} {ι' : Type} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (ι : GA D U →* GA D V × GA D W) (hι : Continuous ι)
    (hgen : ∀ τ', ∀ X ∈ lieAt U τ', ∀ f, IsThetaFunO ψ V W f → ∃ G, IsThetaFunO ψ V W G ∧
      ∀ p z, HasDerivAt (fun t : ℝ => ω (p * ι (oneP θ U τ' X t)) f z) (ω p G z) 0)
    (C : Fr U) (τ : D.what₂.Tau) (E : MvPolynomial ι' ℂ →ₗ[ℂ] (WO V W → ℂ)) (hE : ∀ P, IsThetaFunO ψ V W (E P))
    (hinj : Function.Injective E) (Q : Matrix (Fin U.rank) (Fin U.rank) ℂ → Module.End ℂ (MvPolynomial ι' ℂ))
    (hQ : ∀ X Y, Q (X + Y) = Q X + Q Y) (κ : Matrix (Fin U.rank) (Fin U.rank) ℂ → ℂ)
    (hD : ∀ X ∈ lieAt U τ, ∀ P z, HasDerivAt (fun t : ℝ => ω (ι (oneP θ U τ X t)) (E P) z)
      (E (Q X P + κ X • P) z) 0)
    (x : Bool → ℤ) (sub : Matrix (Fin U.rank) (Fin U.rank) ℂ → MvPolynomial ι' ℂ →ₐ[ℂ] MvPolynomial ι' ℂ)
    (hsub : ∀ h R, cc (sub h R) = cc R)
    (hK : ∀ h ∈ Formalism.REAL.Kset (C.ε τ), ∀ P, ω (ι (C.elt θ τ h)) (E P) =
      (signBlockDeterminant (C.ε τ) true h ^ x true * signBlockDeterminant (C.ε τ) false h ^ x false) • E (sub h P))
    (X : Matrix (Fin U.rank) (Fin U.rank) ℂ) (hX : X ∈ lieAt U τ) :
    κ X = ∑ j, (C.fr τ * X * (C.fr τ)⁻¹) j j * (x (C.ε τ j) : ℂ) - cc (Q X 1) := by
  have hF : IsUnit (C.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (C.fr_unit τ)
  have hG := C.fr_gram τ
  have hP : ∀ X ∈ lieAt U τ, ∀ P p z, HasDerivAt (fun t : ℝ => ω (p * ι (oneP θ U τ X t)) (E P) z)
      (ω p (E (Q X P + κ X • P)) z) 0 := by
    intro X hX P p z
    obtain ⟨G, -, hG'⟩ := hgen τ X hX _ (hE P)
    have e : G = E (Q X P + κ X • P) := by
      funext w
      have h1 := hG' 1 w
      simp only [one_mul, map_one, Module.End.one_apply] at h1
      exact h1.unique (hD X hX P w)
    rw [← e]
    exact hG' p z
  have hadd : ∀ X ∈ lieAt U τ, ∀ Y ∈ lieAt U τ, κ (X + Y) = κ X + κ Y := by
    intro X hX Y hY
    have hXY : X + Y ∈ lieAt U τ := by
      have h1 : Xᴴ * gramAt D U τ + gramAt D U τ * X = 0 := hX
      have h2 : Yᴴ * gramAt D U τ + gramAt D U τ * Y = 0 := hY
      show (X + Y)ᴴ * gramAt D U τ + gramAt D U τ * (X + Y) = 0
      rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1, h2, add_zero]
    let 𝒮 : Set (GA D U → ℂ) := {φ | ∃ f z, IsThetaFunO ψ V W f ∧ φ = fun g => ω (ι g) f z}
    have hc : ∀ φ ∈ 𝒮, Continuous φ := by
      rintro _ ⟨f, z, hf, rfl⟩
      exact (hω.om_cont f hf z).comp hι
    have hd : ∀ φ ∈ 𝒮, ∀ τ', ∀ Z ∈ lieAt U τ', ∃ φ' ∈ 𝒮, ∀ g,
        HasDerivAt (fun t : ℝ => φ (g * oneP θ U τ' Z t)) (φ' g) 0 := by
      rintro _ ⟨f, z, hf, rfl⟩ τ' Z hZ
      obtain ⟨G, hG', h⟩ := hgen τ' Z hZ f hf
      refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
      simpa only [map_mul] using h (ι g) z
    have key : E (Q (X + Y) 1 + κ (X + Y) • 1) = E (Q X 1 + κ X • 1) + E (Q Y 1 + κ Y • 1) := by
      funext z
      exact der_add hθ 𝒮 hc hd (φ := fun g => ω (ι g) (E 1) z) ⟨_, z, hE 1, rfl⟩ hX hY hXY
        (hD X hX 1 z) (hD Y hY 1 z) (hD _ hXY 1 z)
    rw [← map_add] at key
    have k2 := congrArg cc (hinj key)
    rw [hQ] at k2
    simp only [LinearMap.add_apply, map_add, cc_smul_one] at k2
    linear_combination k2
  have h0 : κ 0 = 0 := by
    have h1 : (0 : Matrix (Fin U.rank) (Fin U.rank) ℂ) ∈ lieAt U τ := by
      show (0 : Matrix (Fin U.rank) (Fin U.rank) ℂ)ᴴ * gramAt D U τ + gramAt D U τ * 0 = 0
      simp
    have := hadd 0 h1 0 h1
    rw [add_zero] at this
    linear_combination -this
  have hQ0 : Q 0 = 0 := by
    have := hQ 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hQn : ∀ X, Q (-X) = -Q X := fun X => by
    have := hQ X (-X)
    rw [add_neg_cancel, hQ0] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hlie : ∀ {Z}, (Zᴴ * gramAt D U τ + gramAt D U τ * Z = 0) → Z ∈ lieAt U τ := fun h => h
  have hXl : Xᴴ * gramAt D U τ + gramAt D U τ * X = 0 := hX
  have hKc : κ (partK (C.fr τ) (C.ε τ) X) = ∑ j, (C.fr τ * X * (C.fr τ)⁻¹) j j * (x (C.ε τ j) : ℂ) -
      cc (Q (partK (C.fr τ) (C.ε τ) X) 1) := by
    have hZ := hlie (partK_lie hF hG hXl)
    have e1 : ∀ t : ℝ, ω (ι (oneP θ U τ (partK (C.fr τ) (C.ε τ) X) t)) (E 1) =
        (signBlockDeterminant (C.ε τ) true (NormedSpace.exp (t • (C.fr τ * partK (C.fr τ) (C.ε τ) X * (C.fr τ)⁻¹))) ^ x true *
          signBlockDeterminant (C.ε τ) false (NormedSpace.exp (t • (C.fr τ * partK (C.fr τ) (C.ε τ) X * (C.fr τ)⁻¹))) ^ x false) •
          E 1 := by
      intro t
      have h1 := hK _ (exp_mem_K hF hG hXl t) 1
      rw [map_one (sub _), Fr.elt, exp_frame hF] at h1
      exact h1
    have e2 : E (Q (partK (C.fr τ) (C.ε τ) X) 1 + κ (partK (C.fr τ) (C.ε τ) X) • 1) =
        E ((∑ j, (C.fr τ * partK (C.fr τ) (C.ε τ) X * (C.fr τ)⁻¹) j j * (x (C.ε τ j) : ℂ)) • 1) := by
      funext z
      have h1 := (hasDerivAt_dfac (C.ε τ) x (C.fr τ * partK (C.fr τ) (C.ε τ) X * (C.fr τ)⁻¹)).mul_const (E 1 z)
      have h2 := hD _ hZ 1 z
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      refine h2.unique (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
      simp only [e1, Pi.smul_apply, smul_eq_mul]
    have k2 := congrArg cc (hinj e2)
    simp only [map_add, cc_smul_one, partK_diag hF] at k2
    linear_combination k2
  have hPc : κ (partP (C.fr τ) (C.ε τ) X) = -cc (Q (partP (C.fr τ) (C.ε τ) X) 1) := by
    have hZl := partP_lie hF hG hXl
    have hZ := hlie hZl
    set Z := partP (C.fr τ) (C.ε τ) X with hZdef
    have hnZ : -Z ∈ lieAt U τ := WeylAction.neg_mem_lieAt hZ
    have hnZl : (-Z)ᴴ * gramAt D U τ + gramAt D U τ * (-Z) = 0 := hnZ
    have hu := GlobalTheory.SmoothForms.RealPts.gramAt_unit U τ
    have hJU : cartM (C.fr τ) (C.ε τ) ∈ Formalism.QuantumDeterminants.UH (gramAt D U τ) := cart_mem_UH hF hG
    have hcomm : ∀ t : ℝ, C.elt θ τ (Formalism.REAL.Jm (C.ε τ)) * oneP θ U τ Z t =
        oneP θ U τ (-Z) t * C.elt θ τ (Formalism.REAL.Jm (C.ε τ)) := by
      intro t
      show atTau θ U τ (cartM (C.fr τ) (C.ε τ)) * atTau θ U τ (NormedSpace.exp (t • Z)) =
        atTau θ U τ (NormedSpace.exp (t • (-Z))) * atTau θ U τ (cartM (C.fr τ) (C.ε τ))
      rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ U τ hJU (GlobalTheory.SmoothForms.exp_mem_UH hu (real_lie t hZl)),
        ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ U τ (GlobalTheory.SmoothForms.exp_mem_UH hu (real_lie t hnZl)) hJU,
        exp_conj_self (cart_sq hF) (B' := t • (-Z))]
      rw [Matrix.mul_smul, Matrix.smul_mul, partP_anti hF]
    obtain ⟨dd, hdd⟩ : ∃ dd : ℂ, dd = signBlockDeterminant (C.ε τ) true (Formalism.REAL.Jm (C.ε τ)) ^ x true *
        signBlockDeterminant (C.ε τ) false (Formalism.REAL.Jm (C.ε τ)) ^ x false := ⟨_, rfl⟩
    have hKJ := hK _ (Jm_mem_K (C.ε τ))
    rw [← hdd] at hKJ
    have hE1 : E 1 ≠ 0 := fun h => one_ne_zero (hinj (h.trans (map_zero E).symm))
    have hd0 : dd ≠ 0 := by
      intro h
      have h1 := hKJ 1
      rw [h, zero_smul] at h1
      apply hE1
      have h2 := congrArg (ω (ι (C.elt θ τ (Formalism.REAL.Jm (C.ε τ)))⁻¹)) h1
      rw [map_zero, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply] at h2
      exact h2
    have key : E (sub (Formalism.REAL.Jm (C.ε τ)) (Q Z 1 + κ Z • 1)) = E (Q (-Z) 1 + κ (-Z) • 1) := by
      funext z
      have h1 := hP Z hZ 1 (ι (C.elt θ τ (Formalism.REAL.Jm (C.ε τ)))) z
      have h2 := (hP (-Z) hnZ 1 1 z).const_mul dd
      rw [hKJ, Pi.smul_apply, smul_eq_mul] at h1
      simp only [map_one, Module.End.one_apply] at h2
      have h3 : dd * E (sub (Formalism.REAL.Jm (C.ε τ)) (Q Z 1 + κ Z • 1)) z = dd * E (Q (-Z) 1 + κ (-Z) • 1) z := by
        refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
        have h4 := hKJ 1
        rw [map_one (sub _)] at h4
        beta_reduce
        rw [← map_mul ι, hcomm, map_mul ι, map_mul ω, Module.End.mul_apply, h4, map_smul, Pi.smul_apply, smul_eq_mul,
          one_mul]
      exact mul_left_cancel₀ hd0 h3
    have k2 := congrArg cc (hinj key)
    rw [hsub, hQn] at k2
    simp only [LinearMap.neg_apply, map_add, map_neg, cc_smul_one] at k2
    have k3 := hadd Z hZ (-Z) hnZ
    rw [add_neg_cancel, h0] at k3
    linear_combination (1 / 2 : ℂ) * k2 - (1 / 2 : ℂ) * k3
  have hs := part_add (F := C.fr τ) (ε := C.ε τ) (X := X)
  have h1 := hadd _ (hlie (partK_lie hF hG hXl)) _ (hlie (partP_lie hF hG hXl))
  have h2 := hQ (partK (C.fr τ) (C.ε τ) X) (partP (C.fr τ) (C.ε τ) X)
  rw [hs] at h1 h2
  rw [h1, h2, hKc, hPc, LinearMap.add_apply, map_add]
  ring

end Core

section Final

open scoped Classical

variable {D : D7} {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem sgn_ne (e : Bool) : sgn e ≠ 0 := by cases e <;> simp [sgn]

theorem ptF_laws (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (A : Fr V) (B : Fr W) {f : WO V W → ℂ}
    (hf : IsVacF ψ θ A B f) :
    (∀ (_τ : D.what₂.Tau) P, IsThetaFunO ψ V W (ptF ψ θ A B f P)) ∧
    (∀ v Q, ptF ψ θ A B f Q = 0 → ptF ψ θ A B f (MvPolynomial.pderiv v Q) = 0) ∧
    ∀ v Q, ptF ψ θ A B f Q = 0 → ptF ψ θ A B f (MvPolynomial.X v * Q) = 0 := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have step : ∀ (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) (Q : PolF D W.rank V.rank),
      ptF ψ θ A B f Q = 0 → ptF ψ θ A B f (raiO τ (A.ε τ) (B.ε τ) i j Q) = 0 ∧
        ptF ψ θ A B f (lowO τ (A.ε τ) (B.ε τ) i j Q) = 0 := by
    intro τ i j Q hQ
    obtain ⟨R, L, w, hE, -⟩ := exists_raise_lower A B h hψ τ
    obtain ⟨E, h1, h2, h3⟩ := hE f hf
    have hQ' : E Q = 0 := Subtype.ext (by rw [← h1, hQ]; rfl)
    refine ⟨?_, ?_⟩
    · rw [h1, h2, hQ', map_zero]; rfl
    · rw [h1, h3, hQ', map_zero]; rfl
  have lin : ∀ (c : ℂ) (P : PolF D W.rank V.rank), ptF ψ θ A B f (c • P) = c • ptF ψ θ A B f P := fun c P =>
    map_smul (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) c P
  have neg : ∀ P : PolF D W.rank V.rank, ptF ψ θ A B f (-P) = -ptF ψ θ A B f P := fun P =>
    map_neg (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) P
  refine ⟨fun τ P => ?_, ?_, ?_⟩
  · obtain ⟨R, L, w, hE, -⟩ := exists_raise_lower A B h hψ τ
    obtain ⟨E, h1, -, -⟩ := hE f hf
    rw [h1]
    exact (E P).2
  · rintro ⟨τ, i, j⟩ Q hQ
    obtain ⟨r, l⟩ := step τ i j Q hQ
    by_cases hp : B.ε τ i = A.ε τ j
    · have e : lowO τ (A.ε τ) (B.ε τ) i j Q = sgn (A.ε τ j) • MvPolynomial.pderiv (τ, i, j) Q := by
        simp [lowO, hp]
      rw [e, lin] at l
      exact (smul_eq_zero.1 l).resolve_left (sgn_ne _)
    · have e : raiO τ (A.ε τ) (B.ε τ) i j Q = (-sgn (A.ε τ j)) • MvPolynomial.pderiv (τ, i, j) Q := by
        simp [raiO, hp]
      rw [e, lin] at r
      exact (smul_eq_zero.1 r).resolve_left (neg_ne_zero.2 (sgn_ne _))
  · rintro ⟨τ, i, j⟩ Q hQ
    obtain ⟨r, l⟩ := step τ i j Q hQ
    by_cases hp : B.ε τ i = A.ε τ j
    · have e : raiO τ (A.ε τ) (B.ε τ) i j Q = sgn (A.ε τ j) • (MvPolynomial.X (τ, i, j) * Q) := by
        simp [raiO, hp]
      rw [e, lin] at r
      exact (smul_eq_zero.1 r).resolve_left (sgn_ne _)
    · have e : lowO τ (A.ε τ) (B.ε τ) i j Q = sgn (A.ε τ j) • (MvPolynomial.X (τ, i, j) * Q) := by
        simp [lowO, hp]
      rw [e, lin] at l
      exact (smul_eq_zero.1 l).resolve_left (sgn_ne _)

theorem ptF_one (A : Fr V) (B : Fr W) (f : WO V W → ℂ) : ptF ψ θ A B f 1 = f := GlobalTheory.FockIndep.pure_one _

theorem ptF_zero (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (A : Fr V) (B : Fr W)
    (hf : IsVacF ψ θ A B (0 : WO V W → ℂ)) (P : PolF D W.rank V.rank) : ptF ψ θ A B 0 P = 0 := by
  obtain ⟨-, -, h⟩ := ptF_laws hθ hψ A B hf
  have lin : ∀ (c : ℂ) (P : PolF D W.rank V.rank), ptF ψ θ A B 0 (c • P) = c • ptF ψ θ A B 0 P := fun c P =>
    map_smul (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb 0) c P
  have add : ∀ P P' : PolF D W.rank V.rank, ptF ψ θ A B 0 (P + P') = ptF ψ θ A B 0 P + ptF ψ θ A B 0 P' := fun P P' =>
    map_add (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb 0) P P'
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.C_eq_smul_one, lin, ptF_one, smul_zero]
  | add p q hp hq => rw [add, hp, hq, add_zero]
  | mul_X p v hp =>
    rw [mul_comm]
    exact h v p hp

theorem ptF_injective (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (A : Fr V) (B : Fr W) {f : WO V W → ℂ}
    (hf : IsVacF ψ θ A B f) (h0 : f ≠ 0) :
    Function.Injective (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) :=
  GlobalTheory.FockVecInj.injective_of_pderiv _ (fun h => h0 ((ptF_one A B f).symm.trans h))
    fun v Q hQ => (ptF_laws hθ hψ A B hf).2.1 v Q hQ

theorem wtS_cast {b : ℕ} (ε' : Fin b → Bool) (aT : ℚ) (e : Bool) :
    ((wtS ε' aT e : ℚ) : ℂ) = -(sgn e * (idx ε' : ℂ) / 2) - aT := by
  cases e <;> simp [wtS, sgn] <;> ring

theorem wtT_cast {a : ℕ} (ε : Fin a → Bool) (aS : ℚ) (e : Bool) :
    ((wtT ε aS e : ℚ) : ℂ) = sgn e * (idx ε : ℂ) / 2 + aS := by
  cases e <;> simp [wtT, sgn] <;> ring

theorem trace_fr {n : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F.det) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∑ j, (F * X * F⁻¹) j j = X.trace := by
  change (F * X * F⁻¹).trace = _
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hF, Matrix.one_mul]

theorem fockS_add {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (X Y : Matrix (Fin a) (Fin a) ℂ) :
    fockS τ ε ε' (X + Y) = (fockS τ ε ε' X + fockS τ ε ε' Y : Module.End ℂ (PolF D b a)) := by
  unfold fockS
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem fockT_add {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (X Y : Matrix (Fin b) (Fin b) ℂ) :
    fockT τ ε ε' (X + Y) = (fockT τ ε ε' X + fockT τ ε ε' Y : Module.End ℂ (PolF D b a)) := by
  unfold fockT
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem elt_one (hθ : IsInfFam θ) {U : HSp D} (C : Fr U) (τ : D.what₂.Tau) : C.elt θ τ 1 = 1 := by
  rw [Fr.elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (C.fr_unit τ)),
    GlobalTheory.PointAtPlaceHom.atTau_one hθ]

theorem one_mem_K {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem lieFockAll : ∀ D : D7, GlobalTheory.ChainFr.LieFockAll D := by
  intro D V W A B θ ψ χS χT ω f τ aS aT hθ hω hS hT hf
  have hψ := hω.std
  by_cases h0 : f = 0
  · subst h0
    have z := ptF_zero hθ hψ A B hf
    refine ⟨fun X hX P w => ?_, fun Y hY P w => ?_⟩
    · simp only [z, map_zero, Pi.zero_apply]
      exact hasDerivAt_const _ _
    · simp only [z, map_zero, Pi.zero_apply]
      exact hasDerivAt_const _ _
  obtain ⟨κS, κT, hκ⟩ := GlobalTheory.LieFock.lieFockUpTo D V W A B θ ψ χS χT ω τ hθ hω
  obtain ⟨h1, h2⟩ := hκ f hf
  obtain ⟨x, y, hx, hy, hc⟩ := GlobalTheory.T.compact_subgroups_act_on_fock_vectors_all_signatures D V W A B θ ψ χS χT ω f τ aS aT hθ hω hS hT hf h0
  have hinj := ptF_injective hθ hψ A B hf h0
  have hth := (ptF_laws hθ hψ A B hf).1 τ
  have hFA : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hFB : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have hKS : ∀ X ∈ lieAt V τ, κS X = -((aT : ℂ) * X.trace) := by
    intro X hX
    have e := kappa_core hθ hω (MonoidHom.inl (GA D V) (GA D W)) (continuous_id.prodMk continuous_const)
      (fun τ' X hX f hf => genS hθ hω τ' X hX f hf) A τ (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) hth hinj
      (fun X => fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)))
      (fun X Y => by
        have e : (A.fr τ * (X + Y) * (A.fr τ)⁻¹).map (starRingEnd ℂ) = (A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ) +
            (A.fr τ * Y * (A.fr τ)⁻¹).map (starRingEnd ℂ) := by
          rw [Matrix.mul_add, Matrix.add_mul]
          ext i j
          simp only [Matrix.map_apply, Matrix.add_apply, map_add]
        rw [e, fockS_add]) κS h1 x (fun h => subst τ (A.ε τ) (B.ε τ) (h.map (starRingEnd ℂ)) 1) (fun h R => cc_subst τ _ _ _ _ R)
      (fun h hh P => by
        have := hc h hh 1 (one_mem_K _) P
        rw [elt_one hθ B τ, signBlockDeterminant_one, signBlockDeterminant_one, _root_.one_zpow, _root_.one_zpow, one_mul, mul_one] at this
        exact this) X hX
    rw [e, cc_fockS, ← trace_fr hFA X, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have k1 := lie_entry hFA (A.fr_gram τ) hX j j
    rw [sgn_mul_self] at k1
    rw [Matrix.map_apply, k1]
    have k2 : ((x (A.ε τ j) : ℤ) : ℂ) = ((wtS (B.ε τ) aT (A.ε τ j) : ℚ) : ℂ) := by
      exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) (hx j)
    rw [k2, wtS_cast]
    ring
  have hKT : ∀ Y ∈ lieAt W τ, κT Y = (aS : ℂ) * Y.trace := by
    intro Y hY
    have e := kappa_core hθ hω (MonoidHom.inr (GA D V) (GA D W)) (continuous_const.prodMk continuous_id)
      (fun τ' X hX f hf => genT hθ hω τ' X hX f hf) B τ (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f) hth hinj
      (fun Y => fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹))
      (fun X Y => by rw [Matrix.mul_add, Matrix.add_mul, fockT_add]) κT h2 y
      (fun k => subst τ (A.ε τ) (B.ε τ) ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ).map (starRingEnd ℂ)) k)
      (fun h R => cc_subst τ _ _ _ _ R)
      (fun k hk P => by
        have := hc 1 (one_mem_K _) k hk P
        rw [elt_one hθ A τ, signBlockDeterminant_one, signBlockDeterminant_one, _root_.one_zpow, _root_.one_zpow, one_mul, one_mul] at this
        exact this) Y hY
    rw [e, cc_fockT, ← trace_fr hFB Y, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have k2 : ((y (B.ε τ i) : ℤ) : ℂ) = ((wtT (A.ε τ) aS (B.ε τ i) : ℚ) : ℂ) := by
      exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) (hy i)
    rw [k2, wtT_cast]
    ring
  refine ⟨fun X hX P z => ?_, fun Y hY P z => ?_⟩
  · beta_reduce
    rw [← hKS X hX]
    exact h1 X hX P z
  · beta_reduce
    rw [← hKT Y hY]
    exact h2 Y hY P z

end Final

end GlobalTheory.LieScalar

end
