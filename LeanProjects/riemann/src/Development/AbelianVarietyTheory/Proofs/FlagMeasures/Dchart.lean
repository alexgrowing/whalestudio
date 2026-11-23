import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

def lev (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def wC (k r : ℕ) : Mat k r := bigCell k r (fun _ => 1) 1

def torD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal fun i =>
  if h : i.val < r then x ⟨i.val, h⟩
  else if h' : r + k < i.val then -star (x ⟨2 * r + k - i.val, by omega⟩) else 0

def um {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (X : lieE S) : Matrix (Fin m) (Fin m) ℂ :=
  unrealify (X : EuclideanSpace ℝ (Fin m × Fin m × Bool))

abbrev EE (k r : ℕ) : Type :=
  (lieE (Nset k r) × lieE (Nset k r)) × ((Fin r → ℂ) × lieE (Formalism.FourierDecayAlt.B2.UWb k r))

def chart (k r : ℕ) (v : EE k r) : Mat k r :=
  wC k r * (NormedSpace.exp (-um v.1.1) * bigCell k r (fun a => 1 + v.2.1 a) 1 * NormedSpace.exp (um v.2.2) *
    NormedSpace.exp (um v.1.2))

def dchart (k r : ℕ) (v : EE k r) : Mat k r :=
  -(wC k r * um v.1.1 * wC k r) + torD k r v.2.1 + um v.2.2 + um v.1.2

example : wC 0 1 = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wC, bigCell, esI]

end GlobalTheory.CellDens
