import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyRestrictScalars
import Mathlib
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_homology_restrictScalars_alt : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ), Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  first | exact @GlobalTheory.natCard_homology_restrictScalars | exact GlobalTheory.natCard_homology_restrictScalars | (intros; apply GlobalTheory.natCard_homology_restrictScalars <;> assumption)
