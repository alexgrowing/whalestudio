import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralUnitaryConjugacyLattice
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.CharpolyDvdOfAevalEqZero

open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

instance isLocalRing_intL : IsLocalRing (intL L) :=
  inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)

theorem isCsr_charpoly {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (M J Ji : Matrix (Fin n) (Fin n) R)
    (hJ : Ji * J = 1) (hM : cT s M * J * M = J) : GlobalTheory.UTr.IsCsr s M.charpoly := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hJ' : J * Ji = 1 := mul_eq_one_comm.1 hJ
  let u : (Matrix (Fin n) (Fin n) R)ˣ := ⟨Ji, J, hJ, hJ'⟩
  set N := Ji * cT s M * J with hNdef
  have hNM : N * M = 1 := by
    rw [hNdef, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s M), hM, hJ]
  have hdeg : M.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdegN : N.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hNc : N.charpoly = (cT s M).charpoly := by
    have := Matrix.charpoly_units_conj u (cT s M)
    rw [← Matrix.coe_units_inv] at this
    exact this
  have hmap : M.charpoly.map s = N.charpoly := by
    rw [hNc, ← Matrix.charpoly_map, ← Matrix.charpoly_transpose]; rfl
  have hrev : (M.charpoly.map s).reflect n = N.charpolyRev := by
    rw [hmap, ← Matrix.reverse_charpoly, Polynomial.reverse, hdegN]
  have hdetN : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
  have hNd : N.det = s M.det := by
    have h1 : N.det = (cT s M).det := by
      rw [hNdef, Matrix.det_mul, Matrix.det_mul, mul_comm (Ji.det), mul_assoc, ← Matrix.det_mul, hJ,
        Matrix.det_one, mul_one]
    rw [h1, cT, Matrix.det_transpose, RingHom.map_det]; rfl
  have h0 : M.charpoly.coeff 0 = (-1) ^ n * M.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hs0 : s (M.charpoly.coeff 0) = (-1) ^ n * N.det := by
    rw [h0, map_mul, map_pow, map_neg, map_one, hNd]
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  rw [hdeg, hrev, Matrix.charpolyRev, hs0]
  have hA : (1 - (X : R[X]) • N.map C) * M.map C = -charmatrix M := by
    rw [sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero C) (map_one C),
      charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, neg_sub]; rfl
  have e1 : (1 - (X : R[X]) • N.map C).det * C M.det = (-1) ^ n * M.charpoly := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_mul, hA, Matrix.det_neg, Fintype.card_fin]; rfl
  have e2 : C N.det * C M.det = (1 : R[X]) := by rw [← C_mul, hdetN, C_1]
  rw [C_mul, C_pow, C_neg, C_1]
  linear_combination (-C N.det) * e1 + (1 - (X : R[X]) • N.map C).det * e2

theorem exists_poly_of_commute {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (M x : Matrix (Fin n) (Fin n) O)
    (hs : M.charpoly.Separable) (hc : x * M = M * x) : ∃ p : O[X], x = aeval M p := by
  obtain ⟨v, hv⟩ := GlobalTheory.BCT.UnitStable.exists_cyclic M hs
  set K := GlobalTheory.ClassParam.krylov M v with hK
  have key : ∀ r : Matrix (Fin n) (Fin n) O, r * M = M * r →
      r * K = GlobalTheory.ClassParam.krylov M (r *ᵥ v) := by
    intro r hr
    have hc : Commute r M := hr
    ext i j
    simp only [hK, GlobalTheory.ClassParam.krylov, Matrix.of_apply, Matrix.mul_apply]
    rw [Matrix.mulVec_mulVec, ← (hc.pow_right (j : ℕ)).eq, ← Matrix.mulVec_mulVec]
    rfl
  have hKd : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).1 hv
  set c : Fin n → O := K⁻¹ *ᵥ (x *ᵥ v) with hcdef
  let p : O[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp : aeval M p = ∑ i : Fin n, c i • M ^ (i : ℕ) := by
    simp only [p, map_sum, map_mul, aeval_C, aeval_X_pow, Algebra.smul_def]
  have hpv : aeval M p *ᵥ v = x *ᵥ v := by
    have h1 : aeval M p *ᵥ v = K *ᵥ c := by
      rw [hp]
      ext k
      simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
        hK, GlobalTheory.ClassParam.krylov, Matrix.of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [h1, hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hKd, Matrix.one_mulVec]
  have hpc : aeval M p * M = M * aeval M p := by
    have e1 : aeval M (p * X) = aeval M p * M := by rw [map_mul, aeval_X]
    have e2 : aeval M (X * p) = M * aeval M p := by rw [map_mul, aeval_X]
    rw [← e1, ← e2, mul_comm]
  refine ⟨p, ?_⟩
  have e : x * K = aeval M p * K := by rw [key x hc, key _ hpc, hpv]
  have := congrArg (· * K⁻¹) e
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKd, Matrix.mul_one] using this

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
