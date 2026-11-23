import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexGlMapStandardLatticeOfIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulEsymmCard
open GlobalTheory.LatHecke GlobalTheory.SatakeInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_glMap_standardLattice_of_integral : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K), (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K) → (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ∧ (IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 → IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin) := by
  first | exact @GlobalTheory.LatHecke.relIndex_glMap_std_of_integral | exact GlobalTheory.LatHecke.relIndex_glMap_std_of_integral | (intros; apply GlobalTheory.LatHecke.relIndex_glMap_std_of_integral <;> assumption)
