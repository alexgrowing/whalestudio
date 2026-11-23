import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsProdDenominatorUnitriangularFactors
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMinors_prod_denominator_unitriangular_factors : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u → IsUni u' → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) → IsIntM L (cT L u * S.Zh * u') → ∀ Δ : E, Δ = ∏ l : Fin (r + 2), (if S.D l ≠ 0 then S.D l else 1) → Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD ∧ ∀ i j, L.cj Δ * u i j ∈ L.O ∧ Δ * u' i j ∈ L.O := by
  first | exact @GlobalTheory.OrbitDenom.main | exact GlobalTheory.OrbitDenom.main | (intros; apply GlobalTheory.OrbitDenom.main <;> assumption)
