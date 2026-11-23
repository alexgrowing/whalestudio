import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameDiagonalRatiosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularModulusProductsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

section Alg

variable {K : Type} [Field K] {N : ℕ}

theorem dg_inv_mul_dg (j : Fin N) {γ : K} (hγ : γ ≠ 0) : dg j γ⁻¹ * dg j γ = 1 := by
  unfold dg
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = j
  · subst h; simp [hγ]
  · simp [Function.update_apply, h]

theorem dg_inv (j : Fin N) {γ : K} (hγ : γ ≠ 0) : (dg j γ)⁻¹ = dg j γ⁻¹ :=
  Matrix.inv_eq_left_inv (dg_inv_mul_dg j hγ)

theorem dg_mem (R : Subring K) (j : Fin N) {γ : K} (hγ : γ ∈ R) : dg j γ ∈ R.matrix := by
  intro i i'
  rcases eq_or_ne i i' with rfl | h
  · unfold dg
    rw [Matrix.diagonal_apply_eq]
    by_cases h : i = j
    · subst h; simpa using hγ
    · simp [Function.update_apply, h, one_mem]
  · unfold dg
    rw [Matrix.diagonal_apply_ne _ h]
    exact zero_mem _

theorem smul_dg_inv_mem (R : Subring K) (j : Fin N) {γ t : K} (ht : t ∈ R) (htγ : t / γ ∈ R) :
    t • dg j γ⁻¹ ∈ R.matrix := by
  intro i i'
  rw [Matrix.smul_apply, smul_eq_mul]
  rcases eq_or_ne i i' with rfl | h
  · unfold dg
    rw [Matrix.diagonal_apply_eq]
    by_cases h : i = j
    · subst h; simpa [div_eq_mul_inv] using htγ
    · simpa [Function.update_apply, h] using ht
  · unfold dg
    rw [Matrix.diagonal_apply_ne _ h, mul_zero]
    exact zero_mem _

theorem inv_apply_self_of_blockTriangular {B : Matrix (Fin N) (Fin N) K} (hB : B.BlockTriangular id)
    (hd : B.det ≠ 0) (i : Fin N) : B⁻¹ i i = (B i i)⁻¹ := by
  letI := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.2 hd)
  have hBi : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have h1 : (B * B⁻¹) i i = 1 := by
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · exact eq_inv_of_mul_eq_one_right h1
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hB h, zero_mul]
    · rw [hBi h, mul_zero]
  · simp

end Alg

theorem coh_step (X : Scheme.{0}) [IsIntegral X] (p k a N : ℕ) (M : X → Matrix (Fin N) (Fin N) X.functionField)
    (c : X → Fin N → X.functionFieldˣ) (j : Fin N) (γ : X.functionField) (hγ : γ ≠ 0)
    (hreg : ∀ x, Ov p x → RegAt x γ ∧ RegAt x ((p : X.functionField) ^ a / γ)) (hc : Coh p (k + 1 + a) M c)
    (η : X → Fin (N + 1) → X.functionFieldˣ)
    (hη : ∀ x, Ov p x → ∀ i, Gen (loc x) (gens γ (fun l => (M x)⁻¹ l j) i) (η x i)) :
    ∃ B : X → Matrix (Fin N) (Fin N) X.functionField, (∀ x, Ov p x → (B x).BlockTriangular id ∧
      ∀ i, B x i i = (η x i.castSucc : X.functionField) / η x i.succ) ∧
      Coh p (k + 1) (fun x => dg j γ * M x * B x) fun x i => c x i * η x i.succ / η x i.castSucc := by
  have E : ∀ x, Ov p x → ∃ B : Matrix (Fin N) (Fin N) X.functionField, B.BlockTriangular id ∧
      Fr (loc x) (dg j γ * M x * B) ∧ ∀ i, B i i = (η x i.castSucc : X.functionField) / η x i.succ :=
    fun x hx => (GlobalTheory.T.triangular_frame_diagonal_ratios _ N (loc x) (M x) j γ (fun i => (η x i : X.functionField)) (hc x hx).1
      (hreg x hx).1 hγ (hη x hx)).1
  choose! B hBt hBf hBd using E
  refine ⟨B, fun x hx => ⟨hBt x hx, hBd x hx⟩, fun x hx => ⟨hBf x hx, ?_⟩⟩
  have hMx := (hc x hx).1
  have hM1 := hBf x hx
  have hdet : (B x).det ≠ 0 := by
    have := hM1.1
    rw [Matrix.det_mul] at this
    exact right_ne_zero_of_mul this
  have hBinv : (B x)⁻¹ = (dg j γ * M x * B x)⁻¹ * dg j γ * M x := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, dg_inv j hγ]
    simp only [mul_assoc]
    rw [← mul_assoc (dg j γ⁻¹), dg_inv_mul_dg j hγ, one_mul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hMx.1), mul_one]
  have hBinvMem : (B x)⁻¹ ∈ (loc x).matrix := by
    rw [hBinv]
    exact mul_mem (mul_mem hM1.2.2 (dg_mem _ j (hreg x hx).1)) hMx.2.1
  have hBinvT : (B x)⁻¹.BlockTriangular id := by
    letI := Matrix.invertibleOfIsUnitDet (B x) (isUnit_iff_ne_zero.2 hdet)
    exact Matrix.blockTriangular_inv_of_blockTriangular (hBt x hx)
  refine ((hc x hx).2.and (eventually_mem_matrix hBinvMem)).mono fun z ⟨h1, h2⟩ hz => ?_
  have hMz := (hc z hz).1
  have hM1z := hBf z hz
  have T := h1 hz
  rw [pow_add] at T
  have hbB : ((p : X.functionField) ^ a) • B z ∈ (loc z).matrix := by
    have e : (M z)⁻¹ * (((p : X.functionField) ^ a) • dg j γ⁻¹) * (dg j γ * M z * B z) =
        ((p : X.functionField) ^ a) • B z := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      simp only [mul_assoc]
      rw [← mul_assoc (dg j γ⁻¹), dg_inv_mul_dg j hγ, one_mul, ← mul_assoc,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hMz.1), one_mul]
    rw [← e]
    exact mul_mem (mul_mem hMz.2.2 (smul_dg_inv_mem _ j (pow_mem (natCast_mem _ p) a) (hreg z hz).2)) hM1z.2.1
  have R := (GlobalTheory.T.triangular_modulus_products _ N (loc z) ((p : X.functionField) ^ (k + 1)) ((p : X.functionField) ^ a)
    ((M x)⁻¹ * M z) ((M x)⁻¹ * M z) (fun i => (c x i : X.functionField) / c z i)
    (fun i => (c x i : X.functionField) / c z i) (pow_mem (natCast_mem _ p) _) (pow_mem (natCast_mem _ p) _)).2
    (B x)⁻¹ (B z) hBinvT (hBt z hz) h2 hbB T
  have eA : (dg j γ * M x * B x)⁻¹ * (dg j γ * M z * B z) = (B x)⁻¹ * ((M x)⁻¹ * M z) * B z := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, dg_inv j hγ]
    simp only [mul_assoc]
    rw [← mul_assoc (dg j γ⁻¹), dg_inv_mul_dg j hγ, one_mul]
  have ed : (fun i => (B x)⁻¹ i i * ((c x i : X.functionField) / c z i) * B z i i) = fun i =>
      ((c x i * η x i.succ / η x i.castSucc : X.functionFieldˣ) : X.functionField) /
        ((c z i * η z i.succ / η z i.castSucc : X.functionFieldˣ) : X.functionField) := by
    funext i
    rw [inv_apply_self_of_blockTriangular (hBt x hx) hdet, hBd x hx, hBd z hz]
    push_cast
    field_simp
  rw [← eA, ed] at R
  exact R

end GlobalTheory.LatChain

end
