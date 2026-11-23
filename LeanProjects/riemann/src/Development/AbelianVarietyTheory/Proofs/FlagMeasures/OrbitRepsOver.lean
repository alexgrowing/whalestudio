import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver

theorem orbit_reps_over : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V]
    [Module E V] (H : HermSp M V) (r : ℕ), ∀ P : FPair H r, Equivalence (Datum.Rel (P := P)) ∧ Nonempty (Reps P) ∧
    ∀ (d d' : Datum P) (t : Term V M r), Datum.Rel d d' → Over P d t → Over P d' t := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r P
  have he := GlobalTheory.NonGenericLocalCheck.rel_equiv P
  refine ⟨he, GlobalTheory.NonGenericLocalCheck.reps_nonempty P, ?_⟩
  rintro d d' t hdd' ⟨g, hg, d'', h1, h2⟩
  exact ⟨g, hg, d'', he.trans (he.symm hdd') h1, h2⟩

end GlobalTheory.LocOver
