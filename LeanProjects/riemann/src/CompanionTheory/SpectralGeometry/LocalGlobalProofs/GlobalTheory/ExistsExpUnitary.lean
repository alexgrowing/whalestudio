import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset

namespace GlobalTheory.CompanionTheory.UnitaryExp

open Matrix

set_option backward.isDefEq.respectTransparency false in

theorem map_exp_matrix {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (f : Matrix m m ℂ ≃ₐ[ℂ] Matrix n n ℂ) (hf : Continuous f) (S : Matrix m m ℂ) :
    f (NormedSpace.exp S) = NormedSpace.exp (f S) := by
  let _ : NormedRing (Matrix m m ℂ) := Matrix.instL2OpNormedRing
  let _ : NormedRing (Matrix n n ℂ) := Matrix.instL2OpNormedRing
  let _ : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.instL2OpNormedAlgebra
  let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.instL2OpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix m m ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp f hf S

end GlobalTheory.CompanionTheory.UnitaryExp
