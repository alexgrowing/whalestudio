import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColNumDef
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def lamS (X : Loc) (j : Fin (numSeg X.TT)) : Fin (2 * segS X.TT j + 1 + 1) → X.TT × Bool :=
  Fin.cons (topStart X j, true) (fun a : Fin (2 * segS X.TT j + 1) =>
    if h : (a : ℕ) < 2 * segS X.TT j then (topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0))
    else (topEnd X j, true))

def posS (X : Loc) (j : Fin (numSeg X.TT)) : Fin (2 * segS X.TT j + 1 + 1) → ℤ :=
  Fin.cons ((segStart X.TT j).val : ℤ) (fun a : Fin (2 * segS X.TT j + 1) =>
    if h : (a : ℕ) < 2 * segS X.TT j then ((segStart X.TT j).val : ℤ) + ((segDists X.TT j).get (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) : ℕ)
    else ((segStart X.TT j).val : ℤ) + (segG X.TT j : ℕ))

def LLseg (X : Loc) (j : Fin (numSeg X.TT)) : LiftLetters (Fin (2 * segS X.TT j + 1 + 1)) where
  vec := fun i => (lamS X j i).2
  pos := posS X j

def zS (X : Loc) (j : Fin (numSeg X.TT)) : ℤ := ((segStart X.TT j).val : ℤ) + (segG X.TT j : ℕ)

def phiS (X : Loc) (j : Fin (numSeg X.TT)) :
    Fin (2 * segS X.TT j + 1 + 1) × Fin (1 + X.m) → (X.TT × Bool) × Fin (X.m + 1) :=
  fun v => (lamS X j v.1, Fin.cast (Nat.add_comm 1 X.m) v.2)

end Formalism.MainNotions.ColumnSystems.Pf
