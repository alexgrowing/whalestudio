import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvr
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → UniversallyOpen f → GeometricallyIrreducible f → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProperDvr.isProper_of_specialFibre | exact GlobalTheory.FibreProperDvr.isProper_of_specialFibre | (intros; apply GlobalTheory.FibreProperDvr.isProper_of_specialFibre <;> assumption)
