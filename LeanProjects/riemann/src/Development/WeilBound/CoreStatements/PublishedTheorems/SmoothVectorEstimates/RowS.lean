import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

abbrev V (ι : Type) (a m : ℕ) : Type := UnipotentBlockColumnIndex a (m + 1) (m + 1) → ι → ℂ

def mm (hm : m + 1 < a) : Fin a := ⟨m, by omega⟩

def ix (hm : m + 1 < a) (j : Fin a) (hj : (j : ℕ) < m + 1) : UnipotentBlockColumnIndex a (m + 1) (m + 1) :=
  ⟨(j, ⟨m + 1, hm⟩), hj, le_rfl, le_rfl⟩

def t0 (hm : m + 1 < a) : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ix hm (mm hm) (Nat.lt_succ_self m)

def O (ι : Type) (hm : m + 1 < a) : Set (V ι a m) := {x | ∀ i, x (t0 hm) i ≠ 0}

def rowS (hm : m + 1 < a) (x : V ι a m) : Fin a → ι → ℂ :=
  fun j => if h : (j : ℕ) < m + 1 then x (ix hm j h) else 0

def rowT (hm : m + 1 < a) (x : V ι a m) : Fin a → ι → ℂ :=
  fun j => if h : (j : ℕ) < m + 1 then
    (if (j : ℕ) = m then (x (t0 hm))⁻¹ else -(x (ix hm j h) * (x (t0 hm))⁻¹)) else 0

def sM (hm : m + 1 < a) (x : V ι a m) : LieI ι a :=
  Matrix.of.symm ((1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowS hm x))

def sI (hm : m + 1 < a) (x : V ι a m) : LieI ι a :=
  Matrix.of.symm ((1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowT hm x))

def e (ι : Type) (hm : m + 1 < a) : V ι a m := Pi.single (t0 hm) 1

def xi (hm : m + 1 < a) (h : GL (Fin a) (ι → ℂ)) : V ι a m := fun t => h.val (mm hm) t.1.1

end PositivityTheory.jumpWindows.CornerBlockIndex

end
