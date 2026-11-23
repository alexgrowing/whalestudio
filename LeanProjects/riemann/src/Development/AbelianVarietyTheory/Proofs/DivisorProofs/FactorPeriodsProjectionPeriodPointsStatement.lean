import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_periods_projection_period_points : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R), D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D'.X] (o : D'.OAct O) (e f : O) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (φ : D'.X →+ D₀.X), IsMonHom inc → IsMonHom pr → pr ≫ inc = o.onB.act e → (∀ χ, ∃ u : LB.Gen (CmpLB D' D₀ pr (h χ) χ), Nrm u) → LBIso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ (y : D'.X) (g : GtPtF D' F), GtPtF.IsIota y g → ∃ g' : GtPtF D₀ F, Act D' D₀ pr h g g' ∧ GtPtF.IsIota (φ y) g') → (∀ y, h (φ y) = star e • f • e • y) → (∀ y, D₀.c (φ y) = D'.c y ≫ pr) ∧ ∃ w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left), w.IsGen ∧ ∀ y y' z J J', Good D'.P.L z J → Good D₀.P.L z J' → val (D₀.tau (φ y) (φ y')) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D₀.c (φ y)) (toUnit (TK R) ≫ D₀.c (φ y'))).left z J J' * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.Two.Fac.periods_of_factor | exact GlobalTheory.Mum.Two.Fac.periods_of_factor | (intros; apply GlobalTheory.Mum.Two.Fac.periods_of_factor <;> assumption)
