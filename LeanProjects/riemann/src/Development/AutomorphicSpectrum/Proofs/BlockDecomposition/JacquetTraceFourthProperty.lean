import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparable

open Polynomial GlobalTheory.LeviDesc.Krylov

noncomputable section

namespace GlobalTheory.CompanionTheory.CharpolyConj

def compan {F : Type} [CommRing F] {r : ℕ} (P : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun l j => if (j : ℕ) + 1 = r then -P.coeff l else if (l : ℕ) = (j : ℕ) + 1 then 1 else 0

theorem pow_mulVec_eq {F : Type} [CommRing F] [Nontrivial F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    Matrix.mulVec (y ^ r) e = ∑ l : Fin r, (-y.charpoly.coeff l) • Matrix.mulVec (y ^ (l : ℕ)) e := by
  have hch : Polynomial.aeval y y.charpoly = 0 := Matrix.aeval_self_charpoly y
  have hdeg : y.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim y
  have hmon : y.charpoly.coeff r = 1 := by
    have := y.charpoly_monic.coeff_natDegree
    rwa [hdeg] at this
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ, hmon, one_smul] at hch
  have hy : y ^ r = -∑ l ∈ Finset.range r, y.charpoly.coeff l • y ^ l := eq_neg_of_add_eq_zero_right hch
  rw [hy, Finset.sum_range (fun l => y.charpoly.coeff l • y ^ l), Matrix.neg_mulVec, Matrix.sum_mulVec,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_mulVec, neg_smul]

theorem mul_krylov {F : Type} [CommRing F] [Nontrivial F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * compan y.charpoly := by
  ext i j
  have hl : (y * krylov y e) i j = Matrix.mulVec (y ^ ((j : ℕ) + 1)) e i := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rfl
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · simp only [compan, Matrix.of_apply, if_pos hj, krylov_apply]
    rw [hj, pow_mulVec_eq y e, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [mul_comm]
  · have hlt : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
    simp only [compan, Matrix.of_apply, if_neg hj, krylov_apply]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hlt⟩ : Fin r)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ (j : ℕ) + 1 := fun h => hb (Fin.ext h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h

end GlobalTheory.CompanionTheory.CharpolyConj

theorem GlobalTheory.CompanionTheory.CharpolyConj.main : PositivityTheory.Rg.Tf.Loc.A4 := by
  intro K _ n γ γ' hs hc
  obtain ⟨e, he⟩ := exists_isUnit_det_krylov_of_separable (γ : Matrix (Fin n) (Fin n) K) hs
  obtain ⟨e', he'⟩ := exists_isUnit_det_krylov_of_separable (γ' : Matrix (Fin n) (Fin n) K) (hc ▸ hs)
  have hu := (Matrix.isUnit_iff_isUnit_det _).2 he
  have hu' := (Matrix.isUnit_iff_isUnit_det _).2 he'
  have h1 := GlobalTheory.CompanionTheory.CharpolyConj.mul_krylov (γ : Matrix (Fin n) (Fin n) K) e
  have h2 := GlobalTheory.CompanionTheory.CharpolyConj.mul_krylov (γ' : Matrix (Fin n) (Fin n) K) e'
  rw [hc] at h1
  refine ⟨hu.unit * hu'.unit⁻¹, ?_⟩
  set B := hu.unit with hB
  set B' := hu'.unit with hB'
  have hBv : (B : Matrix (Fin n) (Fin n) K) = krylov (γ : Matrix (Fin n) (Fin n) K) e := rfl
  have hBv' : (B' : Matrix (Fin n) (Fin n) K) = krylov (γ' : Matrix (Fin n) (Fin n) K) e' := rfl
  set C : Matrix (Fin n) (Fin n) K := GlobalTheory.CompanionTheory.CharpolyConj.compan (γ' : Matrix (Fin n) (Fin n) K).charpoly with hC
  have key : ((B⁻¹ * γ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((B'⁻¹ * γ' * B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have a1 : ((B⁻¹ * γ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = C := by
      rw [mul_assoc, Units.val_mul, Units.val_mul, hBv, h1, ← hBv, ← mul_assoc, Units.inv_mul, one_mul]
    have a2 : ((B'⁻¹ * γ' * B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = C := by
      rw [mul_assoc, Units.val_mul, Units.val_mul, hBv', h2, ← hBv', ← mul_assoc, Units.inv_mul, one_mul]
    rw [a1, a2]
  have key' : B⁻¹ * γ * B = B'⁻¹ * γ' * B' := Units.ext key
  calc (B * B'⁻¹)⁻¹ * γ * (B * B'⁻¹) = B' * (B⁻¹ * γ * B) * B'⁻¹ := by group
    _ = B' * (B'⁻¹ * γ' * B') * B'⁻¹ := by rw [key']
    _ = γ' := by group
