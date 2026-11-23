import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticesGlueToVectorBundle
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_lattices_descend : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] (B : GlobalTheory.Vert.Model O) (J : Type) [Finite J] (h : ℕ) (L : J → ∀ U : AffOp B.X, Submodule U.Bp (Fin h → U.Bp)) (T : Set (Σ U : AffOp B.X, U.Bp)), T.Finite → (∀ j U, Module.Finite U.Bp (L j U) ∧ Module.Projective U.Bp (L j U) ∧ ∀ x : Fin h → U.Bp, (p : U.Bp) • x ∈ L j U) → (∀ j (U U' : AffOp B.X) (hle : U'.1 ≤ U.1), L j U' = Submodule.span U'.Bp (piMap (AffOp.res hle) (Fin h) '' (L j U : Set (Fin h → U.Bp)))) → ∃ K' : IntermediateField B.X.functionField (Kbar B.X), FiniteDimensional B.X.functionField K' ∧ (∀ t ∈ T, (t.2 : Kbar B.X) ∈ K') ∧ ∀ j U, IsDescended K' U (L j U) := by
  first | exact @GlobalTheory.BplusDescent.exists_finiteDimensional_isDescended | exact GlobalTheory.BplusDescent.exists_finiteDimensional_isDescended | (intros; apply GlobalTheory.BplusDescent.exists_finiteDimensional_isDescended <;> assumption)
