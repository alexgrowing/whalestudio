import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
open Formalism.IndefR.Datum Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

namespace GlobalTheory.PlusDetONB

open GlobalTheory.CompactFockAction GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

def sgnP {k : ℕ} (p : ℕ) : Fin k → Bool := fun a => decide (a.val < p)

theorem onb_facts {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    B * B⁻¹ = 1 ∧ B⁻¹ * B = 1 ∧ s = B * Formalism.REAL.Jm (sgnP p) * B⁻¹ := by
  obtain ⟨ε, hε, hG, hs⟩ := h
  have hd : Matrix.diagonal (fun a => (ε a : ℂ)) = Formalism.REAL.Jm (sgnP (k := k) p) := by
    unfold Formalism.REAL.Jm sgnP
    congr 1
    funext a
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · have : ¬ a.val < p := by omega
      simp [h1, this]
  have hsq : Matrix.diagonal (fun a => (ε a : ℂ)) * Matrix.diagonal (fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hsq
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hB : B.det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hG, Matrix.det_mul, h0, mul_zero]
  have hU : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hU
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hU
  refine ⟨h1, h2, ?_⟩
  rw [← hd, ← hs, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem isBlock_of_isKMat {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) : IsBlock (sgnP p) κ := by
  intro i j hij
  apply h.2 i j
  intro hiff
  apply hij
  unfold sgnP
  exact decide_eq_decide.2 hiff

theorem card_sgnP {k p : ℕ} (hp : p ≤ k) (e : Bool) :
    (Finset.univ.filter fun i : Fin k => sgnP p i = e).card = if e then p else k - p := by
  have h1 : (Finset.univ.filter fun i : Fin k => i.val < p).card = p := by
    rw [Fin.card_filter_val_lt]; omega
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (p := fun i : Fin k => i.val < p)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  cases e
  · simp only [sgnP, decide_eq_false_iff_not, Bool.false_eq_true, if_false]
    omega
  · simp only [sgnP, decide_eq_true_eq, if_true]
    exact h1

theorem signBlockDeterminant_positive_eq {k p : ℕ} (κ : Matrix (Fin k) (Fin k) ℂ) : signBlockDeterminant (sgnP p) true κ = detPos p κ := by
  unfold signBlockDeterminant detPos
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (fun a : Fin k => (by simp [sgnP] : sgnP p a = true ↔ a.val < p)))]
  rfl

theorem signBlockDeterminant_negative_eq {k p : ℕ} (κ : Matrix (Fin k) (Fin k) ℂ) : signBlockDeterminant (sgnP p) false κ = detNeg p κ := by
  unfold signBlockDeterminant detNeg
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (fun a : Fin k => (by simp [sgnP] : sgnP p a = false ↔ ¬ a.val < p)))]
  rfl

theorem detPlus_onb : ∀ {n m : ℕ} (GS sS BS κS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT κT : Matrix (Fin m) (Fin m) ℂ)
    (pS pT : ℕ), pS ≤ n → pT ≤ m → IsONBasis GS sS BS pS → IsONBasis GT sT BT pT → IsKMat pS κS → IsKMat pT κT →
    GlobalTheory.WeilParts.detPlus sS sT (BS * κS * BS⁻¹)⁻¹ (BT * κT * BT⁻¹) =
      detPos pT κT ^ pS * detNeg pT κT ^ (n - pS) * (detPos pS κS ^ pT)⁻¹ * (detNeg pS κS ^ (m - pT))⁻¹ := by
  intro n m GS sS BS κS GT sT BT κT pS pT hpS hpT hBS hBT hκS hκT
  obtain ⟨h1S, h2S, hsS⟩ := onb_facts hBS
  obtain ⟨h1T, h2T, hsT⟩ := onb_facts hBT
  have hu : κS * κSᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκS.1
  have hinv : (BS * κS * BS⁻¹)⁻¹ = BS * κSᴴ * BS⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    calc BS * κS * BS⁻¹ * (BS * κSᴴ * BS⁻¹) = BS * (κS * (BS⁻¹ * BS) * κSᴴ) * BS⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2S, Matrix.mul_one, hu, Matrix.mul_one, h1S]
  rw [hinv, hsS, hsT, detPlus_conj h2S h2T]
  have bS := isBlock_of_isKMat hκS
  have bT := isBlock_of_isKMat hκT
  have bS' : IsBlock (sgnP pS) κSᴴ := fun i j e => by
    rw [Matrix.conjTranspose_apply, bS j i (Ne.symm e), star_zero]
  rw [detPlus_block bS' bT, prod_bool _ fun e => signBlockDeterminant (sgnP pS) e κSᴴ,
    prod_bool _ fun e => signBlockDeterminant (sgnP pT) e κT, card_sgnP hpT, card_sgnP hpT, card_sgnP hpS, card_sgnP hpS]
  have ih := fun e => signBlockDeterminant_mul_eq_one_of_mul_eq_one e bS hu
  rw [eq_inv_of_mul_eq_one_right (ih true), eq_inv_of_mul_eq_one_right (ih false)]
  simp only [if_true, Bool.false_eq_true, if_false, signBlockDeterminant_positive_eq, signBlockDeterminant_negative_eq, inv_pow]
  ring

end GlobalTheory.PlusDetONB
