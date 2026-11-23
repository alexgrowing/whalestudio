import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationForm_psi_balanced_symmetric_periodForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (Q : P.D.toPre.X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), QForm.IsQ P.D.toPre ϖ Q ∧ (∀ a, 0 ≤ Q a) ∧ (∀ a b, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = QForm.bOf P.D.toPre Q a b) ∧ (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧ ∀ (C : Type) [NormedField C] (f : V →+* C) (p : ℕ), Function.Injective f → (∀ a, ‖f a‖ ≤ 1) → ∀ a b, betaAt P.D.toPre f p a b = -Real.logb p ‖f ϖ‖ * (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b := by
  first | exact @GlobalTheory.ValForm.main | exact GlobalTheory.ValForm.main | (intros; apply GlobalTheory.ValForm.main <;> assumption)
