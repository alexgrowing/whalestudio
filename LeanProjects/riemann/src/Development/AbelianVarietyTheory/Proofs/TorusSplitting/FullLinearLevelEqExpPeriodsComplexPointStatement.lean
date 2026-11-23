import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FullLinearLevelEqExpPeriodsComplexPoint
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLinearLevel_eq_exp_periods_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)), IsPeriod (Fu.Di i) ty Pm → y.x = Fu.u i Pm → ∀ (N : ℕ), 0 < N → ∀ ev : LatMod Dw N → (ptO Xo y.x ⟶ Xo.univ.t.G), IsFullLev Xo N y.x ev → ∃ a : LatMod Dw N → (Fu.Di i).La, (∀ q, (ev q).left = (Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a q))).left ∧ ev q ^ N = 1) ∧ ∀ (n : ℕ) (z : Fin n → LatMod Dw N), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ u : (Fu.Di i).La, ∃ (cf : Fin n → 𝓞 E) (v : (Fu.Di i).La), u = ∑ b, cf b • a (z b) + N • v := by
  first | exact @GlobalTheory.fullLevel_eq_exp_periods | exact GlobalTheory.fullLevel_eq_exp_periods | (intros; apply GlobalTheory.fullLevel_eq_exp_periods <;> assumption)
