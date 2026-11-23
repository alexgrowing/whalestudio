import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedLatticesFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_lattices_family : ∀ (X X' : Scheme.{0}) [IsIntegral X] (f : X' ⟶ X) (K' : IntermediateField X.functionField (Kbar X)) (γ : ∀ U : AffOp X, Γ(X', f ⁻¹ᵁ U.1) →+* U.Bp), (∀ U, Function.Injective (γ U)) → (∀ (U U' : AffOp X) (hle : U'.1 ≤ U.1) (a : Γ(X', f ⁻¹ᵁ U.1)), γ U' ((X'.presheaf.map (homOfLE (f.preimage_mono hle)).op).hom a) = AffOp.res hle (γ U a)) → (∀ U, (γ U).range = ringOver K' U) → ∀ (h c : ℕ), (c : Kbar X) ≠ 0 → ∀ (L : ∀ U : AffOp X, Submodule U.Bp (Fin h → U.Bp)), (∀ U, IsDescended K' U (L U) ∧ ∀ x : Fin h → U.Bp, (c : U.Bp) • x ∈ L U) → (∀ (U U' : AffOp X) (hle : U'.1 ≤ U.1), L U' = Submodule.span U'.Bp (piMap (AffOp.res hle) (Fin h) '' (L U : Set (Fin h → U.Bp)))) → ∀ (U U' : AffOp X) (hle : U'.1 ≤ U.1), (L U').comap (piMap (γ U') (Fin h)) = Submodule.span Γ(X', f ⁻¹ᵁ U'.1) (piMap (resG X' (f.preimage_mono hle)) (Fin h) '' ((L U).comap (piMap (γ U) (Fin h)) : Set (Fin h → Γ(X', f ⁻¹ᵁ U.1)))) := by
  first | exact @GlobalTheory.LatGlue.comap_eq_span_res | exact GlobalTheory.LatGlue.comap_eq_span_res | (intros; apply GlobalTheory.LatGlue.comap_eq_span_res <;> assumption)
