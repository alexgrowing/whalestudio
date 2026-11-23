import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_double_coset_term_basic_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → IsSD L S.Hm Λ ∧ S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 ∧ S.M d Λ ≤ S.sat Λ ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j})) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j})) ∧ LinearIndependent E (Sum.elim (S.fr d Λ) (S.fr' d Λ)) ∧ S.IsIntCls (S.Fr d Λ) ∧ ∀ d', S.IsTerm d' Λ → d' = d := by
  first | exact @GlobalTheory.HL.TermBasic.term_basic | exact GlobalTheory.HL.TermBasic.term_basic | (intros; apply GlobalTheory.HL.TermBasic.term_basic <;> assumption)
