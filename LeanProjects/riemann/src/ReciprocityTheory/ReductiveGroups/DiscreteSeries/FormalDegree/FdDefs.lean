import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def Dvec (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) - ((a : ℕ) : ℝ)

def lamT (lam : Fin n → ℝ) (t : ℕ) : Fin n → ℝ := lam + (t : ℝ) • Dvec n

def Vand (lam : Fin n → ℝ) : ℝ := ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)

end ReciprocityTheory.ChartRestriction.DS
