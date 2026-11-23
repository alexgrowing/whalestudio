import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeight
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unf_section_norm_bound_at_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ) (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (t : ℝ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → (∀ k (τ' : E →+* ℂ), ‖τ' (U.X k).ξ0‖ = x) → s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) → IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ t → ∀ z ∈ GlobalTheory.AllWt.framesOn U Z, (∀ hz : z.2 ∈ (U.X z.1).dom, GlobalTheory.FlatLine.Tested (U.un z.1 ⟨z.2, hz⟩)) → GlobalTheory.AllWt.homN U x (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0) s z = Real.exp t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge | exact GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge <;> assumption)
