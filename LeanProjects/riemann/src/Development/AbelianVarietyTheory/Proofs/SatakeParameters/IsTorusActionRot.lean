import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar

set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n k : ℕ} (A : HolAtlas M n)

structure IsTorusAction (act : (Fin k → UnitAddCircle) → M → M) : Prop where

  cont : Continuous fun p : (Fin k → UnitAddCircle) × M => act p.1 p.2

  smooth : ∀ i j, ContDiffOn ℝ ∞
    (fun q : (Fin k → ℝ) × V n => A.e i (act (fun a => ((q.1 a : ℝ) : UnitAddCircle)) ((A.e j).symm q.2)))
    {q | q.2 ∈ (A.e j).target ∧ act (fun a => ((q.1 a : ℝ) : UnitAddCircle)) ((A.e j).symm q.2) ∈ (A.e i).source}

  holo : ∀ t, A.IsHolo A (act t)

  zero : ∀ y, act 0 y = y

  add : ∀ s t y, act (s + t) y = act s (act t y)

def torusAvg (act : (Fin k → UnitAddCircle) → M → M) (α : A.Fld) : A.Fld := fun x =>
  ∑ S, (∫ t, (bas n).repr (A.pullback A (act t) α x) S) • bas n S

def TypeGe (p : ℕ) (α : A.Fld) : Prop :=
  ∀ x S, (bas n).repr (α x) S ≠ 0 → p ≤ (S.filter (·.val < n)).card

def rot (t : Fin 1 → UnitAddCircle) (v : V 1) : V 1 := (AddCircle.toCircle (t 0) : ℂ) • v

end GlobalTheory.CxForm.HolAtlas
