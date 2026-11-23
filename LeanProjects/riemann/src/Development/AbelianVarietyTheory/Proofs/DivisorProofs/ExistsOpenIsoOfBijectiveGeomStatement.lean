import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIsoOfBijectiveGeom
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_iso_of_bijective_geom : ∀ (K : Type) [Field K] [CharZero K] (X T : Scheme.{0}) [IsIntegral X] [IsIntegral T] (f : X ⟶ T) (q : T ⟶ Spec (.of K)), LocallyOfFiniteType f → LocallyQuasiFinite f → IsSeparated f → QuasiCompact f → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T), ∃! x : Spec (.of Ω) ⟶ X, x ≫ f = t) → ∃ U : T.Opens, Nonempty U ∧ IsIso (f ∣_ U) := by
  first | exact @GlobalTheory.isIso_restrict_of_bijective_geomPts | exact GlobalTheory.isIso_restrict_of_bijective_geomPts | (intros; apply GlobalTheory.isIso_restrict_of_bijective_geomPts <;> assumption)
