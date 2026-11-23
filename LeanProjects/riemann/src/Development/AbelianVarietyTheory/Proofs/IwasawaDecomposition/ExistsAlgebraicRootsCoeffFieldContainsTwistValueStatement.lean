import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgebraicRootsCoeffFieldContainsTwistValue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicRoots_coeffFieldContainsTwistValues : ∃ Sv : ∀ P : Pre, Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ, (∀ P Ξ, ∀ z ∈ Sv P Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), I.Ok → (∀ z ∈ Sv B.toPre (Set.range I.xi), z ∈ B.LLC) → ValsIn I := by
  first | exact @GlobalTheory.Mem.Col2.exists_roots_valsIn | exact GlobalTheory.Mem.Col2.exists_roots_valsIn | (intros; apply GlobalTheory.Mem.Col2.exists_roots_valsIn <;> assumption)
