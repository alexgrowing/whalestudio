import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnesses
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ n₀ ∈ S.N, ∃ n₀' ∈ S.N', ∃ n'' ∈ S.N', (∀ v, n₀ v = eich L S.Hm x u s v) ∧ (∀ v, n₀⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v, n₀' v = eich L S.Hm x' u s v) ∧ (∀ v ∈ perp L S.Hm S.X', n'' v = v) ∧ ((n₀⁻¹ • Λ : Submodule L.O S.V) : Set S.V) = S.moved Λ x u s ∧ S.IsTermW d (n₀⁻¹ • Λ) (n₀⁻¹ * (S.wit d Λ).1) (n'' * n₀' * (S.wit d Λ).2) := by
  first | exact @GlobalTheory.HL.MoveWit.main | exact GlobalTheory.HL.MoveWit.main | (intros; apply GlobalTheory.HL.MoveWit.main <;> assumption)
