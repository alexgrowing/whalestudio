import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.BaseChangeAssembly

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.TransposeInverse

open Ad3.R (G2 dia2 LInv)

theorem ti_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (a b : GL n R) :
    ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

end GlobalTheory.CompanionTheory.TransposeInverse

end
