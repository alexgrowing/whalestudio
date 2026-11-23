import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamily
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_automorphism_period_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (KA l).val.toRingHom ty) (s : Sim Dw) (ρ : Xo.X ≅ Xo.X), IsTypeFn H Dw.p Dw.q ty → Xo.LevAut s ρ → (∀ i, ∃ i', ∀ P, IsPeriod (F.Di i) ty P → ∃ P', IsPeriod (F.Di i') ty P' ∧ F.u i P ≫ ρ.hom = F.u i' P') ∧ ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → F.u i P ≫ ρ.hom = F.u i P' → ∃ γ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b, (F.Di i).EF (γ a) (γ b) = (F.Di i).EF a b) ∧ ∀ a, γ (F.t i (s.f l.M a)) - F.t i a ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di i).La) := by
  first | exact @GlobalTheory.LevStab.levAut_component | exact GlobalTheory.LevStab.levAut_component | (intros; apply GlobalTheory.LevStab.levAut_component <;> assumption)
