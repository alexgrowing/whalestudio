import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteD
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_irreducible_properSpecialFibre_completeDvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of O)), IrreducibleSpace X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → (∃ x : X, f x = IsLocalRing.closedPoint O) → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre | exact GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre | (intros; apply GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre <;> assumption)
