import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunction
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZero_section_of_periodSpace_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), 1 ≤ D.p + D.q → (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → FnAlgClosed Xo c → ∀ v : Fin F.n → c.F, ∃ f ∈ sec Xo c 0 0, (∀ m : ℕ, (∀ i, v i ^ m = 1) → f ^ m = 1) ∧ ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P, IsPeriod (F.Di i) ty P → y.x = F.u i P → Formalism.L2.PjFree.toC (evR Xo c f y) = σ (v i) := by
  first | exact @GlobalTheory.CompFun.exists_section_of_function | exact GlobalTheory.CompFun.exists_section_of_function | (intros; apply GlobalTheory.CompFun.exists_section_of_function <;> assumption)
