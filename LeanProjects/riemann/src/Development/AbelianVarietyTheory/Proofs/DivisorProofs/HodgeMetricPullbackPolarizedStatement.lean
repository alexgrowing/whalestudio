import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricPullbackPolarized
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_metric_pullback_polarized : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (q : T ⟶ Sp (𝓞 κ.c.F)), b ≫ s.T.Z.s = q → ∀ (Q : Out.PolAV T) (θ : Q.A.left ⟶ s.T.Z.t.G.left) (hθ : IsGrpPullback Q.A s.T.Z.t.G b θ), LBIso (s.T.Z.t.PP.L.pull θ) Q.L → ∀ h : VMetric q (LieVB.omega Q.A) Q.g, (PPAS.ofPolAV Q).IsHodge h → ∀ (α : (Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G) ≅ LieVB.omega Q.A), α.hom = LieVB.omegaBase hθ → ∀ h₀ : VMetric q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) Q.g, h₀.IsIsometry h α → IsDualEigOn (fun σ' => x.hodge σ') b h₀ := by
  first | exact @GlobalTheory.PullHodge.isDualEigOn_hodge | exact GlobalTheory.PullHodge.isDualEigOn_hodge | (intros; apply GlobalTheory.PullHodge.isDualEigOn_hodge <;> assumption)
