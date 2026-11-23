import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSplittingRestricts
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_splitting_restricts : ∀ (X : Scheme.{0}) [IsIntegral X] (U V : AffOp X) (hle : V.1 ≤ U.1) (h n : ℕ) (L : Submodule U.Bp (Fin h → U.Bp)) (L' : Submodule V.Bp (Fin h → V.Bp)) (g : Fin n → Fin h → U.Bp) (S : Fin n → Fin h → Kbar X), L' = Submodule.span V.Bp (piMap (AffOp.res hle) (Fin h) '' (L : Set (Fin h → U.Bp))) → Splits U L g S → Splits V L' (fun k => piMap (AffOp.res hle) (Fin h) (g k)) S := by
  first | exact @GlobalTheory.BplusDescent.splits_restrict | exact GlobalTheory.BplusDescent.splits_restrict | (intros; apply GlobalTheory.BplusDescent.splits_restrict <;> assumption)
