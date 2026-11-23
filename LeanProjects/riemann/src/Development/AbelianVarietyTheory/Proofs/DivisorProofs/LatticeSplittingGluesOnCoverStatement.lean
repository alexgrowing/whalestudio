import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSplittingGluesOnCover
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_splitting_glues_on_cover : ∀ (X : Scheme.{0}) [IsIntegral X] (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) (h m : ℕ) (a : Fin m → Γ(X, U.1)) (V : Fin m → AffOp X) (hle : ∀ k, (V k).1 ≤ U.1) (L : Submodule U.Bp (Fin h → U.Bp)) (L' : ∀ k, Submodule (V k).Bp (Fin h → (V k).Bp)) (n : Fin m → ℕ) (g : ∀ k, Fin (n k) → Fin h → (V k).Bp) (S : ∀ k, Fin (n k) → Fin h → Kbar X), Ideal.span (Set.range a) = ⊤ → L.FG → (∀ k (x : (V k).Bp), ∃ (N : ℕ) (r : U.Bp), (r : Kbar X) = algebraMap Γ(X, U.1) (Kbar X) (a k) ^ N * x) → (∀ k, L' k = Submodule.span (V k).Bp (piMap (AffOp.res (hle k)) (Fin h) '' (L : Set (Fin h → U.Bp)))) → (∀ k, Splits (V k) (L' k) (g k) (S k)) → (∀ k l i, ((g k l i : (V k).Bp) : Kbar X) ∈ K') → (∀ k l i, S k l i ∈ K') → ∃ (n' : ℕ) (g' : Fin n' → Fin h → U.Bp) (S' : Fin n' → Fin h → Kbar X), Splits U L g' S' ∧ (∀ l i, (g' l i : Kbar X) ∈ K') ∧ ∀ l i, S' l i ∈ K' := by
  first | exact @GlobalTheory.BplusDescent.Glue.splits_glue | exact GlobalTheory.BplusDescent.Glue.splits_glue | (intros; apply GlobalTheory.BplusDescent.Glue.splits_glue <;> assumption)
