import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEqZeroOfLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero : ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q)), (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) - freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0 → (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.relation_kernel
  | exact GlobalTheory.EtC.KummerSplit.relation_kernel
  | (intros; apply GlobalTheory.EtC.KummerSplit.relation_kernel <;> assumption)
