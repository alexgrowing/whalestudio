import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharacterCoxeterTorusInvEqAtInverseStatement

open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.TypeCharacterConjugateInverse

theorem toSquareBlock_mul_of_blockTriangular {r : ℕ} {k : Type} [Field k] {A B : Matrix (Fin r) (Fin r) k}
    {b : Fin r → Fin r} (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (c : Fin r)
    [Fintype {i : Fin r // b i = c}] :
    A.toSquareBlock b c * B.toSquareBlock b c = (A * B).toSquareBlock b c := by
  classical
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.mul_apply, Matrix.of_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l => b l = c) (p := fun l => b l = c) (by simp)
    (fun l => A i.1 l * B l j.1)]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_
  have hl' : b l ≠ c := by simpa using hl
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hA (show b l < b i.1 by rw [i.2]; exact h), zero_mul]
  · rw [hB (show b j.1 < b l by rw [j.2]; exact h), mul_zero]

theorem blockTriangular_inv {r : ℕ} {k : Type} [Field k] {b : Fin r → Fin r} (z : GL (Fin r) k)
    (hz : (z : Matrix (Fin r) (Fin r) k).BlockTriangular b) :
    ((z⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular b := by
  letI := z.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hz

theorem toSquareBlock_mul_inv {r : ℕ} {k : Type} [Field k] {b : Fin r → Fin r} (z : GL (Fin r) k)
    (hz : (z : Matrix (Fin r) (Fin r) k).BlockTriangular b) (c : Fin r)
    [Fintype {i : Fin r // b i = c}] [DecidableEq {i : Fin r // b i = c}] :
    (z : Matrix (Fin r) (Fin r) k).toSquareBlock b c *
      ((z⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).toSquareBlock b c = 1 := by
  rw [toSquareBlock_mul_of_blockTriangular hz (blockTriangular_inv z hz), ← Units.val_mul, mul_inv_cancel,
    Units.val_one]
  ext i j
  simp [Matrix.toSquareBlock_def, Matrix.one_apply, Subtype.ext_iff]

theorem typeChar_conj_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (r : ℕ) (s : LevelCuspCharacters.SSParam p K r),
    (∀ x y : GL (Fin r) (ZMod p), IsConj x y → LevelCuspCharacters.typeChar s x = LevelCuspCharacters.typeChar s y) ∧
    ∀ x : GL (Fin r) (ZMod p),
      LevelCuspCharacters.typeChar (⟨s.1, fun c => (s.2 c)⁻¹⟩ : LevelCuspCharacters.SSParam p K r) x = LevelCuspCharacters.typeChar s x⁻¹ := by
  intro p _ K _ r s
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    unfold LevelCuspCharacters.typeChar
    congr 1
    letI := Fintype.ofFinite (GL (Fin r) (ZMod p))
    refine Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun y => ?_
    have h : (Equiv.mulLeft c y)⁻¹ * (c * x * c⁻¹) * (Equiv.mulLeft c y) = y⁻¹ * x * y := by
      simp only [Equiv.coe_mulLeft]
      group
    rw [h]
  · unfold LevelCuspCharacters.typeChar
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    have h : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    rw [h]
    generalize y⁻¹ * x * y = z
    by_cases hz : (z : Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1
    · rw [if_pos hz, if_pos (blockTriangular_inv z hz)]
      refine Finset.prod_congr rfl fun c _ => ?_
      exact GlobalTheory.T.greenCuspidalCharacterCoxeterTorus_inv_eq_at_inverse p K _ (s.2 c) _ _ (toSquareBlock_mul_inv z hz c.1)
    · rw [if_neg hz, if_neg fun h' => hz (by simpa using blockTriangular_inv z⁻¹ h')]

end GlobalTheory.TypeCharacterConjugateInverse
