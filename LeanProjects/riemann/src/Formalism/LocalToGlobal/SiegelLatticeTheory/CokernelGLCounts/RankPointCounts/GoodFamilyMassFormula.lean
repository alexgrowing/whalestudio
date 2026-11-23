import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.GoodFamilyMass

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

def StepDataOne (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d'

def StepDataMove (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d d' : Datum P), Datum.Rel d d' → (∃ t : Term V M r, IsTermOver P d' t) →
          ∃ t : Term V M r, IsTermOver P d t

def StepTermOne (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d t' → TRel P t t'

def StepMuPos (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → 0 < mu P t

def StepWtPos (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d0 d : Datum P) (t : Term V M r), IsTermOver P d t → 0 < Datum.wt d0 d

def GoodFamilyMassFormula (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        ∀ (R : Reps P) (d0 : Datum P), 0 < nn R d0 ∧ nn R d0 ≠ ⊤

section Idx

variable {G : Type*} [Group G]

end Idx

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

end Formalism.L2.SG.GoodFamilyMass
