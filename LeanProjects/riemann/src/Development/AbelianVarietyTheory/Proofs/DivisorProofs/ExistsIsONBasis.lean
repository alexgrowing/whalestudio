import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameLawsTheta

open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (realOf movS frameFn Fam)
open scoped ComplexOrder

theorem exists_isONBasis {n : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) :
    ∃ (p : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), IsONBasis G s B p := by
  obtain ⟨p, q, B, B', hBB', hB'B, hG, hs⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n G s h.1 h.2.1 h.2.2
  have hpq : p + q = n := by
    have h1 : Fintype.card (Fin n) ≤ Fintype.card (Fin p ⊕ Fin q) := by
      calc Fintype.card (Fin n) = (1 : Matrix (Fin n) (Fin n) ℂ).rank := (Matrix.rank_one).symm
        _ = (B * B').rank := by rw [hBB']
        _ ≤ B'.rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card (Fin p ⊕ Fin q) := Matrix.rank_le_card_height _
    have h2 : Fintype.card (Fin p ⊕ Fin q) ≤ Fintype.card (Fin n) := by
      calc Fintype.card (Fin p ⊕ Fin q) = (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).rank := (Matrix.rank_one).symm
        _ = (B' * B).rank := by rw [hB'B]
        _ ≤ B.rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_height _
    simp only [Fintype.card_fin, Fintype.card_sum] at h1 h2
    omega
  subst hpq
  let e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  have hd : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
      Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply] <;> split_ifs <;> simp
  have he : ∀ a : Fin (p + q), Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) (e a) =
      ((if (a : ℕ) < p then 1 else -1 : ℤ) : ℂ) := by
    intro a
    refine Fin.addCases (fun i => ?_) (fun j => ?_) a
    · simp [e, i.isLt]
    · simp [e]
  refine ⟨p, B.submatrix id e, fun a => if (a : ℕ) < p then 1 else -1, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : (a : ℕ) < p
    · exact Or.inl ⟨by simp [ha], ha⟩
    · exact Or.inr ⟨by simp [ha], by omega⟩
  · have : (B.submatrix id e)ᴴ * G * B.submatrix id e = (Bᴴ * G * B).submatrix e e := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
        Matrix.submatrix_id_id, Matrix.conjTranspose_submatrix]
    rw [this, hG, hd, Matrix.submatrix_diagonal_equiv]
    congr 1; funext a; rw [Function.comp_apply, he a]; split_ifs with hh <;> simp [hh]
  · have : s * B.submatrix id e = (s * B).submatrix id e := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
    rw [this, hs, hd]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, id]
    erw [Matrix.mul_diagonal]
    rw [he j]
    split_ifs <;> simp

variable {D : D7}

end GlobalTheory.FrameLawsTheta

end
