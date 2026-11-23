import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedLatticeFiniteProjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_lattice_finite_projective : ∀ (X : Scheme.{0}) [IsIntegral X] (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) (A : Type) [CommRing A] (γ : A →+* U.Bp), Function.Injective γ → γ.range = ringOver K' U → ∀ (h : ℕ) (L : Submodule U.Bp (Fin h → U.Bp)), IsDescended K' U L → Module.Finite A (L.comap (piMap γ (Fin h))) ∧ Module.Projective A (L.comap (piMap γ (Fin h))) := by
  first | exact @GlobalTheory.LatGlue.finite_projective_comap_of_isDescended | exact GlobalTheory.LatGlue.finite_projective_comap_of_isDescended | (intros; apply GlobalTheory.LatGlue.finite_projective_comap_of_isDescended <;> assumption)
