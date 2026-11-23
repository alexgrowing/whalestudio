import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblIdent

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Matrix in
theorem fromRows_add_fromRows {R : Type} [Add R] {m₁ m₂ n : Type} (A B : Matrix m₁ n R) (C D : Matrix m₂ n R) :
    fromRows A C + fromRows B D = fromRows (A + B) (C + D) := by
  ext (i | i) j <;> rfl

open Matrix in
theorem smul_fromRows {R S : Type} [SMul S R] {m₁ m₂ n : Type} (s : S) (A : Matrix m₁ n R) (C : Matrix m₂ n R) :
    s • fromRows A C = fromRows (s • A) (s • C) := by
  ext (i | i) j <;> rfl

theorem nT_eq {R : Type} [CommRing R] {d : ℕ} (h c : R) (hh : h * 2 = 1) (X Y : Matrix (Fin d) (Fin d) R)
    (h2 : (Y + 1) * (X + 1) = 1) (hc : (c * c) • X = X) :
    ((h * h * h) • ((1 - c) • X - (1 + c) • Y)) * (1 + (h * (1 + c)) • X) = (h * h) • X := by
  have hYX : Y * X = -X - Y := by
    have e : Y * X + X + Y = 0 := by
      have := h2; rw [add_mul, mul_add, mul_add, mul_one, one_mul, one_mul] at this
      rw [← sub_eq_zero] at this; rw [← this]; abel
    rw [← sub_eq_zero, ← e]; abel
  have hY : (c * c) • Y = Y := by
    have e : Y = -((Y + 1) * X) := by
      rw [add_mul, one_mul, hYX]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, hc]
  have hXX : (c * c) • (X * X) = X * X := by rw [← Matrix.smul_mul, hc]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul,
    smul_sub, smul_add, smul_smul, Matrix.mul_sub]
  linear_combination (norm := module) (-(h ^ 4 * (1 + c) ^ 2)) • hYX - h ^ 4 • hXX + h ^ 4 • hc + h ^ 4 • hY +
    hh • ((h ^ 3 * (1 + c) + h ^ 2) • X + (h ^ 3 * (1 + c)) • Y)

theorem blocks {R : Type} [CommRing R] {d : ℕ} (h c : R) (hh : h * 2 = 1) (K N T : Matrix (Fin d) (Fin d) R)
    (hT : T = 1 + (h * (1 + c)) • (K - 1)) (hNT : N * T = (h * h) • (K - 1)) :
    (1 + (h * c) • (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-1 : Matrix (Fin d) (Fin d) R))ᵀ)) *
        Matrix.fromBlocks K 0 0 (1 : Matrix (Fin d) (Fin d) R) * Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) =
      (1 + Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-1 : Matrix (Fin d) (Fin d) R) * N * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R))ᵀ) *
        Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) * T := by
  simp only [Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg, Matrix.add_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.fromRows_mul,
    Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_add, smul_fromRows,
    fromRows_add_fromRows, hNT]
  rw [Matrix.fromRows_inj.eq_iff]
  subst hT
  constructor
  · linear_combination (norm := module) hh • (-(h + 1) • (K - 1))
  · linear_combination (norm := module) hh • (h • (K - 1))

end GlobalTheory.SplitDblIdent

namespace GlobalTheory.SplitDblGen

theorem half_mul_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    (half : AE F E) * 2 = 1 := by
  rw [half, show (2 : AE F E) = algebraMap (AF F) (AE F E) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self,
    map_one]

theorem diagonalFixingDoubling_mul_firstFactor_lagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → K' * K = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d * Matrix.fromBlocks K 0 0 1 * diagCols (E := AE F E) (Fin d) =
      GlobalTheory.SplitDblGen.nMat c K K' * diagCols (E := AE F E) (Fin d) * GlobalTheory.SplitDblGen.tMat c K := by
  intro F E _ _ _ _ _ d c K K' _ h2 hc
  have hNT := GlobalTheory.SplitDblIdent.nT_eq half c half_mul_two (K - 1) (K' - 1) (by simpa using h2) hc
  exact GlobalTheory.SplitDblIdent.blocks half c half_mul_two K (splitDoublingNBlock c K K') (tMat c K) rfl hNT

end GlobalTheory.SplitDblGen
end
