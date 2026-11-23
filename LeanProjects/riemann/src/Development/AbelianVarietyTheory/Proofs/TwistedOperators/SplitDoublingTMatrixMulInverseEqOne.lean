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

namespace GlobalTheory.SplitDblGen

theorem tMat_mul_tMat_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  intro F E _ _ _ _ _ d c K K' hKK hc
  have h2 : (half : AE F E) * 2 = 1 := by
    unfold half
    rw [show (2 : AE F E) = algebraMap (AF F) (AE F E) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self, map_one]
  have hP : (c * c) • ((K - 1) * (K' - 1)) = (K - 1) * (K' - 1) := by rw [← smul_mul_assoc, hc]
  have hsum : (K - 1) + (K' - 1) + (K - 1) * (K' - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hKK]; noncomm_ring
  have hff : ((half * (1 + c)) * (half * (1 + c))) • ((K - 1) * (K' - 1))
      = (half * (1 + c)) • ((K - 1) * (K' - 1)) := by
    rw [show (half * (1 + c)) * (half * (1 + c)) = half * half * (1 + 2 * c) + half * half * (c * c) by ring,
      add_smul, ← smul_smul (half * half) (c * c), hP, ← add_smul]
    congr 1
    linear_combination (half * (1 + c)) * h2
  unfold tMat
  generalize half * (1 + c) = f at hff ⊢
  have e : (1 + f • (K - 1)) * (1 + f • (K' - 1))
      = 1 + f • ((K - 1) + (K' - 1)) + (f * f) • ((K - 1) * (K' - 1)) := by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, smul_add]; abel
  rw [e, hff, add_assoc, ← smul_add, hsum, smul_zero, add_zero]

end GlobalTheory.SplitDblGen
