import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_stalk_ne_infty_of_no_generization : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (w : X), (∀ y ∈ GlobalTheory.QCoh.support F, w ∈ closure ({y} : Set X) → y = w) → Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ := by
  first | exact @GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation | exact GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation | (intros; apply GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation <;> assumption)
