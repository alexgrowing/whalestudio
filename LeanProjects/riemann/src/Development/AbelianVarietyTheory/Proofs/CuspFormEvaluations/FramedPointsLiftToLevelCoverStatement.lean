import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoints_lift_to_levelCover : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (y : FrPt Xo c S) (x₂ : Sp S ⟶ d.Xo₂.X), x₂ ≫ d.r = y.x → x₂ ≫ d.Xo₂.s = sOf d.c₂ S → ∃ y₂ : FrPt d.Xo₂ d.c₂ S, y₂.x = x₂ ∧ FrOver d y₂ y) ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (T : Type) [CommRing T] [Algebra c.F T] [Algebra d.c₂.F T], (∀ a : c.F, algebraMap d.c₂.F T (d.eF a) = algebraMap c.F T a) → ∀ (ψ : S →ₐ[c.F] T) (ψ₂ : S →ₐ[d.c₂.F] T), ψ₂.toRingHom = ψ.toRingHom → ∀ (y : FrPt Xo c S) (y₂ : FrPt d.Xo₂ d.c₂ S) (z : FrPt Xo c T) (z₂ : FrPt d.Xo₂ d.c₂ T), FrOver d y₂ y → FrMap ψ y z → FrMap ψ₂ y₂ z₂ → FrOver d z₂ z) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrOver d y₂' y' → y₂'.x = y₂.x → FrBor t y y' → FrBor t y₂ y₂' := by
  first | exact @GlobalTheory.frames_lift_to_cover | exact GlobalTheory.frames_lift_to_cover | (intros; apply GlobalTheory.frames_lift_to_cover <;> assumption)
