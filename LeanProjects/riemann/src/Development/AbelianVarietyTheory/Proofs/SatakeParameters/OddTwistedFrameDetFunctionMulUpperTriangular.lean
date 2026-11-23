import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SgRevNeZero
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem upper_inv_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hU : ∀ r s, s < r → M r s = 0) (hd : ∀ r, M r r ≠ 0) :
    (∀ r s, s < r → M⁻¹ r s = 0) ∧ ∀ r, M⁻¹ r r = (M r r)⁻¹ := by
  classical
  have hB : Matrix.BlockTriangular M id := fun i j h => hU i j h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hB]
    exact Finset.prod_ne_zero_iff.2 fun r _ => hd r
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  letI := M.invertibleOfIsUnitDet hunit
  have hBi : Matrix.BlockTriangular M⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun r s h => hBi h, fun i => ?_⟩
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hunit) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single i] at h
  · exact eq_inv_of_mul_eq_one_right h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hU i k hk, zero_mul]
    · rw [hBi hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem zT_mul {n : ℕ} (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos (fun τ => x τ * β τ) = fun τ => zT X D pos x τ *
      (if IsOddPos (pos.symm τ).2 then ((β τ)⁻¹).transpose.submatrix Fin.rev Fin.rev else β τ) := by
  funext τ
  unfold zT
  split_ifs with h
  · rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    exact (Equiv.sum_comp Fin.revPerm (fun k => ((x τ)⁻¹).transpose i k * ((β τ)⁻¹).transpose k (Fin.rev j))).symm
  · rfl

theorem prod_inv_rev_zpow_mul_prod_pow_eq_odd_position {n : ℕ} (b : Fin n → ℂ) (hb : ∀ r, b r ≠ 0) (c : ℤ) (ν : Fin n → ℕ) (h : ∀ r, (ν r : ℤ) ≤ c) :
    (∏ r, (b (Fin.rev r))⁻¹) ^ (-c) * ∏ r, (b (Fin.rev r))⁻¹ ^ ν r = ∏ r, b r ^ (c - (ν (Fin.rev r) : ℤ)).toNat := by
  rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  rw [← Equiv.prod_comp Fin.revPerm (fun r => b r ^ (c - (ν (Fin.rev r) : ℤ)).toNat)]
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  have e : b (Fin.rev r) ^ (c - (ν r : ℤ)).toNat = b (Fin.rev r) ^ (c - (ν r : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by linarith [h r])]
  rw [e, inv_zpow', neg_neg, inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hb _)]
  congr 1

theorem twF_mul_bor : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∀ (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (x τ).det ≠ 0) → IsBor β → twF X D pos c Q (fun τ => x τ * β τ) = (∏ τ, ∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) * twF X D pos c Q x := by
  intro p _ X D pos n ν c hνc Q hQ x β _hx hβ
  classical
  have hbd : ∀ τ r, β τ r r ≠ 0 := fun τ r => (hβ τ).2 r
  have hinv : ∀ τ, (∀ r s, s < r → ((β τ)⁻¹) r s = 0) ∧ ∀ r, ((β τ)⁻¹) r r = (β τ r r)⁻¹ :=
    fun τ => upper_inv_diag (β τ) (hβ τ).1 (hbd τ)
  let β' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    if IsOddPos (pos.symm τ).2 then ((β τ)⁻¹).transpose.submatrix Fin.rev Fin.rev else β τ
  have hd' : ∀ τ r, β' τ r r = if IsOddPos (pos.symm τ).2 then (β τ (Fin.rev r) (Fin.rev r))⁻¹ else β τ r r := by
    intro τ r
    simp only [β']
    split_ifs
    · simp [(hinv τ).2]
    · rfl
  have hB' : IsBor β' := by
    intro τ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp only [β']
      split_ifs
      · simp only [Matrix.submatrix_apply, Matrix.transpose_apply]
        exact (hinv τ).1 _ _ (Fin.rev_lt_rev.2 hsr)
      · exact (hβ τ).1 r s hsr
    · rw [hd']
      split_ifs
      · exact inv_ne_zero (hbd τ _)
      · exact hbd τ r
  have hz : zT X D pos (fun τ => x τ * β τ) = fun τ => zT X D pos x τ * β' τ := zT_mul X D pos x β
  have hev : GL3Theta.evFr D Q (fun τ => zT X D pos x τ * β' τ) =
      (∏ τ, ∏ r, β' τ r r ^ ν τ r) * GL3Theta.evFr D Q (zT X D pos x) := by
    have h1 := Formalism.L2.KerInert.SharpPolyP.sp_eval_colSub β' (zT X D pos x) Q
    rw [hQ β' hB', MvPolynomial.smul_eval] at h1
    exact h1.symm
  have key : ∀ τ, (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) * ∏ r, β' τ r r ^ ν τ r
      = (∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) *
        (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ).det ^ (-(c τ)) else 1) := by
    intro τ
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [if_pos ho]
      rw [Matrix.det_mul, Formalism.L2.KerInert.SharpPolyP.sp_det_bor hB', mul_zpow]
      simp only [hd', if_pos ho]
      rw [← prod_inv_rev_zpow_mul_prod_pow_eq_odd_position (fun r => β τ r r) (hbd τ) (c τ) (ν τ) (hνc τ)]
      ring
    · simp only [if_neg ho, one_mul, mul_one, hd']
  unfold twF
  rw [hz, hev]
  calc (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) *
        ((∏ τ, ∏ r, β' τ r r ^ ν τ r) * GL3Theta.evFr D Q (zT X D pos x))
      = (∏ τ, (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) * ∏ r, β' τ r r ^ ν τ r) *
          GL3Theta.evFr D Q (zT X D pos x) := by rw [Finset.prod_mul_distrib]; ring
    _ = _ := by simp_rw [key]; rw [Finset.prod_mul_distrib]; ring

end GlobalTheory.TwV.DelA
