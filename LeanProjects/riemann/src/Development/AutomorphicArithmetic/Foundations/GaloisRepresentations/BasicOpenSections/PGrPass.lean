import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.BlockProjectionMultiplicative

variable {d : ℕ} {L : Type} [Field L]

private def blkPart (c : Fin d → ℕ) (M : Matrix (Fin d) (Fin d) L) : Matrix (Fin d) (Fin d) L :=
  fun i j => if c i = c j then M i j else 0

private theorem blkPart_add (c : Fin d → ℕ) (M N : Matrix (Fin d) (Fin d) L) :
    blkPart c (M + N) = blkPart c M + blkPart c N := by
  ext i j
  simp only [blkPart, Matrix.add_apply]
  split_ifs <;> simp

private theorem blkPart_smul (c : Fin d → ℕ) (a : L) (M : Matrix (Fin d) (Fin d) L) :
    blkPart c (a • M) = a • blkPart c M := by
  ext i j
  simp only [blkPart, Matrix.smul_apply]
  split_ifs <;> simp

private theorem blkPart_one (c : Fin d → ℕ) : blkPart c (1 : Matrix (Fin d) (Fin d) L) = 1 := by
  ext i j
  simp only [blkPart]
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

private theorem blkPart_mul (c : Fin d → ℕ) {M N : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (hN : N.BlockTriangular c) :
    blkPart c (M * N) = blkPart c M * blkPart c N := by
  ext i j
  rw [Matrix.mul_apply]
  change (if c i = c j then (M * N) i j else 0) =
    ∑ k, (if c i = c k then M i k else 0) * (if c k = c j then N k j else 0)
  by_cases h : c i = c j
  · rw [if_pos h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : c i = c k
    · have h2 : c k = c j := h1.symm.trans h
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1, zero_mul]
      rcases lt_or_gt_of_ne h1 with h3 | h3
      · have h4 : c j < c k := h ▸ h3
        rw [hN h4, mul_zero]
      · rw [hM h3, zero_mul]
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : c i = c k
    · have h2 : ¬ c k = c j := fun e => h (h1.trans e)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private theorem blkTri_pow (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (n : ℕ) : (M ^ n).BlockTriangular c := by
  induction n with
  | zero => rw [pow_zero]; exact Matrix.blockTriangular_one
  | succ n ih => rw [pow_succ]; exact ih.mul hM

private theorem blkPart_pow (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (n : ℕ) : blkPart c (M ^ n) = blkPart c M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blkPart_one]
  | succ n ih => rw [pow_succ, pow_succ, blkPart_mul c (blkTri_pow c hM n) hM, ih]

private theorem blkPart_aeval (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (P : Polynomial L) :
    blkPart c (Polynomial.aeval M P) = Polynomial.aeval (blkPart c M) P := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, map_add, blkPart_add, hp, hq]
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
      blkPart_smul, blkPart_pow c hM]

end UpperTheory.Gal.Mod.BlockProjectionMultiplicative

open UpperTheory.Gal.Mod.BlockProjectionMultiplicative in
theorem UpperTheory.Gal.Mod.grPass :
    GrPass := by
  intro Γ L _ _ d ρ₀ ρ hG g P h0
  obtain ⟨c, hc⟩ := hG
  obtain ⟨hT, hD⟩ := hc g
  have e : (ρ g : Matrix (Fin d) (Fin d) L) = blkPart c (ρ₀ g : Matrix (Fin d) (Fin d) L) := by
    ext i j
    exact hD i j
  rw [e, ← blkPart_aeval c hT, h0]
  ext i j
  simp [blkPart]
