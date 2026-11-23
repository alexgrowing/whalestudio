import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMatrixCongruenceContentJacobian
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMatrix_congruence_content_jacobian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) E), IsUnit A.det → (∀ X, X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X) ∧ ∀ B, IsCO (hermLat L m) B → IsCO (hermLat L m) ((fun X => cT L A * X * A) '' B) ∧ cont (hermLat L m) ((fun X => cT L A * X * A) '' B) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * m)) * cont (hermLat L m) B := by
  first | exact @GlobalTheory.HL.HermJacobian.cont_congr | exact GlobalTheory.HL.HermJacobian.cont_congr | (intros; apply GlobalTheory.HL.HermJacobian.cont_congr <;> assumption)
