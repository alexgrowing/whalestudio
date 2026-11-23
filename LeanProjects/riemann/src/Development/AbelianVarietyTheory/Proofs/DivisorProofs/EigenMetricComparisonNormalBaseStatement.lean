import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenMetricComparisonNormalBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_comparison_normal_base : ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (M : DRBase O c) (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp (𝓞 D.what₂.LL)) (E E' : (D.host.E →+* ℂ) → B.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ)) (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (H : ∀ σ, (h σ).IsCInf) (H' : ∀ σ, (h' σ).IsCInf) (u : ∀ σ, E σ ⟶ E' σ), IsArithVar q (dimGr D.what₂.Tau O.N O.j) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → (∀ σ, IsoHom (h σ) (h' σ) (u σ)) → ∀ (Bg : Scheme.{0}) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z) (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB) (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB), PairAt O R c q E E' h h' u jB πB t t' (fun σ' => M.x.eigMetAt σ' (some R)) → ∀ (β : B ⟶ M.B) (w : β ≫ strL M = q), jB ≫ β ≫ M.b = πB ≫ genι O.s.T.Z → β (genericPoint B) = genericPoint M.B → ∀ h₀ : VMetric (strL M) ((Scheme.Modules.pullback M.b).obj (GlobalTheory.LieVB.omega O.s.T.Z.t.G)) (D.R.f * O.N), SameMet (intEquiv O) ((M.h R).pull M.b rfl) h₀ → IsGraded (h₀.dual.pull β w) (Fintype.equivFin (D.host.E →+* ℂ)) h u := by
  first | exact @GlobalTheory.LieFilt.isGraded_lie | exact GlobalTheory.LieFilt.isGraded_lie | (intros; apply GlobalTheory.LieFilt.isGraded_lie <;> assumption)
