import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldMapSurjectiveOfMono
import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueFieldMap_surjective_of_mono' : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X), Function.Surjective (f.residueFieldMap x).hom := by
  first | exact @GlobalTheory.residueFieldMap_surjective_of_mono | exact GlobalTheory.residueFieldMap_surjective_of_mono | (intros; apply GlobalTheory.residueFieldMap_surjective_of_mono <;> assumption)
