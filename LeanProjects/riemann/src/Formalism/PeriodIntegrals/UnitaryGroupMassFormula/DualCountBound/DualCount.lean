import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.MemISub

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Q

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

abbrev satQ (Λ : Submodule M.L.O V) {ι : Type} (v : ι → V) : Submodule M.L.O V :=
  Λ ⊓ (Submodule.span E (Set.range v)).restrictScalars M.L.O

abbrev QQ (Λ : Submodule M.L.O V) {ι : Type} (v : ι → V) : Type :=
  ↥(satQ Λ v) ⧸ (Submodule.span M.L.O (Set.range v)).comap (satQ Λ v).subtype

abbrev CokQ {ι : Type} [Fintype ι] (G : Matrix ι ι M.L.O) : Type :=
  (ι → M.L.O) ⧸ LinearMap.range G.mulVecLin

end Q

def FamLam (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          ∀ j, H.MMfam t j ∈ t.abelian₂

def FamIndep (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          LinearIndependent E (H.MMfam t)

def LamInt (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O

def GramEq (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          (H.gram (H.MMfam t)).det = (H.gram P.MMgen).det

def MinorInt (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          ∀ l, P.Dm l ∈ M.L.O

def DualCount : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (ι : Type) [Fintype ι] [DecidableEq ι]
      (v : ι → V) (Λ : Submodule M.L.O V), LinearIndependent E v → (∀ j, v j ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) → IsUnit (H.gram v).det →
      ∀ G : Matrix ι ι M.L.O, (∀ a b, (G a b : E) = H.gram v a b) → Finite (CokQ G) →
        Finite (QQ Λ v) ∧ Nat.card (QQ Λ v) ^ 2 ≤ Nat.card (CokQ G)

def MatIdx : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι M.L.O) (δ : 𝒪[F]), δ ≠ 0 →
      ((G.det : M.L.O) : E) = algebraMap F E (δ : F) →
      Finite (CokQ G) ∧ Nat.card (CokQ G) ≤ Nat.card (M.L.O ⧸ Ideal.span {toO M δ})

def HaarIdx : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ δ : 𝒪[F], δ ≠ 0 → M.modK (algebraMap F E (δ : F)) * (Nat.card (M.L.O ⧸ Ideal.span {toO M δ}) : ℝ) ≤ 1

def ModLe : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ x ∈ M.R, M.modK x ≤ 1

def ModZero : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    M.modK 0 = 0

def InR : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ y : 𝒪[F], algebraMap F E (y : F) ∈ M.R

def FixO : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ x ∈ M.L.O, M.L.cj x = x → ∃ y : 𝒪[F], algebraMap F E (y : F) = x

end PI.NGStepBBW
