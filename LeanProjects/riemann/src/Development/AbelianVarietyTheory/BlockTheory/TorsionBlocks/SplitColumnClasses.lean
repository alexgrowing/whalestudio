import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  p.Prime ∧ (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E

theorem splitsCompletely_g (D : D7) (i : Fin 2) : SplitsCompletely D.host.E (D.host.g i) :=
  ⟨D.host.g_prime i, D.nd.g_split i⟩

def ColClassSet (D : D7) (L : LevelData D) (u : D.what₂.Word) : Type :=
  letI := D.host.cmStar
  ClassSet
    ((ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
      (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    ((L u).U.subgroupOf (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))

theorem card_colClassSet (D : D7) (L : LevelData D) (u : D.what₂.Word) :
    Nat.card (ColClassSet D L u) = Nat.card ((D.mem u).C.cls 0) := by
  letI := D.host.cmStar
  exact (Nat.card_eq_of_bijective _ (L u).y_bij).symm

def ClassCount (D : D7) (L : LevelData D) (u : D.what₂.Word) : Prop :=
  (Nat.card (ColClassSet D L u) : ℝ) =
    Formalism.MainNotions.StandardLattice.massI D D.R.k * Formalism.MainNotions.StandardLattice.idxPi D (D.host.g 0) (D.host.g 1) *
      ((((D.mem u).A.T : ℕ) : ℝ) ^ D.R.k - 1) ^ D.R.f

def ColumnClassNumber : Prop :=
  ∀ (D : D7) (L : LevelData D) (u : D.what₂.Word),
    (∀ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i) →
    (∀ i : Fin 2, SplitsCompletely D.host.E (D.host.g i)) →
    SplitsCompletely D.host.E (D.mem u).A.T →
    ClassCount D L u

end GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

end
