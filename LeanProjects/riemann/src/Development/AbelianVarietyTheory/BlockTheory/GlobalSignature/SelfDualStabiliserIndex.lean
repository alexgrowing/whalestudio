import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SatakeDualWeyl.StatementC
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    dualSet σ J N = (N : Set (n → E))

def stabK (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k)
      (TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E),
      IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N →
      (Lv u).U ≤ stabK D N →
      (((Lv u).U.relIndex (stabK D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def IndexKU : Prop := ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

def ExistsSelfDualOver : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    SplitsF D (D.mem u).A.T →
      ∃ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E),
        IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N ∧ (Lv u).Lb ≤ N ∧
        (Lv u).U ≤ stabK D N

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex
