import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

def PowQ : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F], IsNonarchimedeanLocalField F →
    ∀ (N : Type) [AddCommGroup N] [Module 𝒪[F] N], Finite N → ∃ i : ℕ, Nat.card N = qF F ^ i

def FinBB (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          Finite (BB H t)

def BoundBB (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          Finite (BB H t) → (be H t : ℝ) ≤ P.Hp

end PI.NGStepBBW
