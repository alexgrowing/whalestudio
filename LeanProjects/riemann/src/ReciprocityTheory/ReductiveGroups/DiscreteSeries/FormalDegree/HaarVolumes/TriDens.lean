import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

abbrev UNgrp (N : ℕ) : Subgroup (Matrix (Fin N) (Fin N) ℂ)ˣ := UJ (fun _ : Fin N => true)

abbrev TriCo (N : ℕ) : Type := (Fin N → ℝ) × ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)

def upMat (t : TriCo N) : Matrix (Fin N) (Fin N) ℂ := fun a b =>
  if a = b then ((t.1 a : ℝ) : ℂ) else if h : a < b then t.2 ⟨(a, b), h⟩ else 0

def triCoOf (M : Matrix (Fin N) (Fin N) ℂ) : TriCo N :=
  (fun j => (M j j).re, fun ab => M ab.1.1 ab.1.2)

def triPos (N : ℕ) : Set (TriCo N) := {t | ∀ j, 0 < t.1 j}

abbrev UCo (N : ℕ) : Type := (Fin N → ℝ) × ({ab : Fin N × Fin N // ab.2 < ab.1} → ℂ)

def skMat (x : UCo N) : Matrix (Fin N) (Fin N) ℂ := fun a b =>
  if a = b then Complex.I * ((x.1 a : ℝ) : ℂ)
  else if h : b < a then x.2 ⟨(a, b), h⟩
  else if h' : a < b then -star (x.2 ⟨(b, a), h'⟩) else 0

def gmDens (N : ℕ) (Z : Fin N → Fin N → ℂ) : ENNReal :=
  ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (-(2 * (N : ℤ))))

def gmMeas (N : ℕ) : Measure (Fin N → Fin N → ℂ) := volume.withDensity (gmDens N)

def triDens (t : TriCo N) : ENNReal :=
  ENNReal.ofReal (∏ j : Fin N, t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1)))

def triMeas (N : ℕ) : Measure (TriCo N) := (volume.restrict (triPos N)).withDensity triDens

def qrMap (kt : UNgrp N × TriCo N) : Fin N → Fin N → ℂ :=
  Matrix.of.symm (toM kt.1 * upMat kt.2)

def qrWt (t : TriCo N) : ℝ := ∏ j : Fin N, t.1 j ^ (2 * (N - (j : ℕ)) - 1)

def chartWR (p : UCo N × TriCo N) : Fin N → Fin N → ℂ :=
  Matrix.of.symm (NormedSpace.exp (skMat p.1) * (1 + upMat p.2))

end ReciprocityTheory.ChartRestriction.DS
