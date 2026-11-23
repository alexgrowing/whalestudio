import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionActsByScalarOnIrrChar
import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] (e : MonoidAlgebra ℂ G), (∀ x y : G, e.coeff (y * x * y⁻¹) = e.coeff x) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x := by
  first | exact @GlobalTheory.classFun_char_scalar | exact GlobalTheory.classFun_char_scalar | (intros; apply GlobalTheory.classFun_char_scalar <;> assumption)
