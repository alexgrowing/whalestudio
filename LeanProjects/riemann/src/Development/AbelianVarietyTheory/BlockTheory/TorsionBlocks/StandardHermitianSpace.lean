import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice NumberField Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def intVecs (D : D7) (n : ℕ) : Set (Fin n → D.host.E) :=
  {x | ∀ a, x a ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)}

def IsStdSpace {D : D7} (V : HSp D) : Prop :=
  V.gram = 1 ∧ L0c D V = intVecs D V.rank

def VStd (D : D7) : Prop :=
  ∀ i : Fin D.R.m, IsStdSpace (Vc D i)

variable {D : D7}

theorem rank_eq (i : Fin D.R.m) : (Vc D i).rank = D.R.nV :=
  D.sp.V_rank _ (Nat.le_add_left 1 _) i.isLt

theorem baseLat_eq {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (i : Fin D.R.m) :
    (L.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = L0c D (Vc D i) := by
  obtain ⟨c, hc⟩ := hL.βV i
  unfold Formalism.IndefR.Lev.IsBaseFrame at hc
  obtain ⟨-, -, -, h1, h2⟩ := hc
  ext x
  constructor
  · intro hx
    simpa using h2 x hx
  · intro hx
    simpa using h1 x hx

end GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace

end
