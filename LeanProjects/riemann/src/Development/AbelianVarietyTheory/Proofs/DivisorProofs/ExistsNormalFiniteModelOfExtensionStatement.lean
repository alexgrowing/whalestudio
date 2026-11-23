import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteModelOfExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finite_model_of_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (K' : IntermediateField B.X.functionField (Kbar B.X)), FiniteDimensional B.X.functionField K' → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (γ : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ IsFinite f.f ∧ (∀ U, Function.Injective (γ U)) ∧ (∀ (U : AffOp B.X) (a : Γ(B.X, U.1)), γ U ((f.f.app U.1).hom a) = algebraMap Γ(B.X, U.1) U.Bp a) ∧ (∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (a : Γ(B'.X, f.f ⁻¹ᵁ U.1)), γ U' ((B'.X.presheaf.map (homOfLE (f.f.preimage_mono hle)).op).hom a) = AffOp.res hle (γ U a)) ∧ ∀ U, (γ U).range = ringOver K' U := by
  first | exact @GlobalTheory.BplusDescent.exists_normalization_in | exact GlobalTheory.BplusDescent.exists_normalization_in | (intros; apply GlobalTheory.BplusDescent.exists_normalization_in <;> assumption)
