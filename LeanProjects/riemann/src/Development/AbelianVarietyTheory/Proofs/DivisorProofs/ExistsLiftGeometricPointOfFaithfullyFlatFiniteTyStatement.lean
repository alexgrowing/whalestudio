import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricPointOfFaithfullyFlatFiniteTy
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_geometricPoint_of_faithfullyFlat_finiteType : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  first | exact @GlobalTheory.GeomPointLift.exists_lift | exact GlobalTheory.GeomPointLift.exists_lift | (intros; apply GlobalTheory.GeomPointLift.exists_lift <;> assumption)
