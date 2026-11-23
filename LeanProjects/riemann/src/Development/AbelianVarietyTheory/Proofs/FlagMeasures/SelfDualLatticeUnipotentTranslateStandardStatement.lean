import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_unipotent_translate_standard : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ Λ, IsSD L S.Hm Λ → ∀ n ∈ S.Nof g, (∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g (r + 1)) ↔ x ∈ Submodule.span L.O (Set.range fun b => n (g b))) → ∃ A, S.IsInner g gs A ∧ ∃ n₁ ∈ S.Nof g, (∀ b, n₁ (g b) = n (g b)) ∧ Λ = n₁ • S.stdLat g gs A := by
  first | exact @GlobalTheory.HL.FrameLift.lift | exact GlobalTheory.HL.FrameLift.lift | (intros; apply GlobalTheory.HL.FrameLift.lift <;> assumption)
