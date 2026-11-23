import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeUOperatorRationalInvertibleRamifiedForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.HermitianColumns.SymAll
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUOperator_rational_invertible_ramifiedForms : ∀ (X : Stages), Nonempty (PreX X.B.toPre) → ∀ (H : Formalism.L2.Herm.ColsHermS X.toD7) (T : ∀ u, Formalism.L2.Forms.Forms0 X.toD7 u), (∀ u, Formalism.L2.Forms.Joint0 H.base.lev0 u (T u)) → (∀ u i v h x, ∃ r : X.B.LL, X.B.embLL r = (T u).gl.psi0 i v h x) → ∀ u (w : X.toD7.what₂.places.Pl), X.toD7.what₂.places.resChar w = (X.toD7.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL X.toD7 u, X.toD7.nuIn u (n • x) ∈ LT.Nlam X.toD7 u w) ∧ ∀ x, X.toD7.nuIn u x ∈ LT.Nlam X.toD7 u w → InLoc (X.toD7.plEq w) (DV.MramL X.toD7 u) (n • x) := by
  first | exact @GlobalTheory.LevelHecke.commensurable_at_level | exact GlobalTheory.LevelHecke.commensurable_at_level | (intros; apply GlobalTheory.LevelHecke.commensurable_at_level <;> assumption)
