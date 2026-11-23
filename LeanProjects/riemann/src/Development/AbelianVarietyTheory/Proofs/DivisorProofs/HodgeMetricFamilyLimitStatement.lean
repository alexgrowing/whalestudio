import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricFamilyLimit
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
theorem _root_.GlobalTheory.T.hodge_metric_family_limit : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (q : T ⟶ Sp (𝓞 κ.c.F)), b ≫ s.T.Z.s = q → (∀ w : T, b w ∈ abLocus s.T.Z.t.G) → ∀ (h : ℝ → VMetric q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) (D.R.f * N)) (h₀ : VMetric q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) (D.R.f * N)), VB.IsVB (LieVB.omega s.T.Z.t.G) (D.R.f * N) → (∀ R, (h R).IsCInf) → h₀.IsCInf → (∀ R, IsDualEigOn (fun σ' => x.eigMetAt σ' (some R)) b (h R)) → IsDualEigOn (fun σ' => x.hodge σ') b h₀ → VFam (fun R => R ^ (-x.kap)) h h₀ := by
  first | exact @GlobalTheory.MetFam.InterpFam.vFam_interp | exact GlobalTheory.MetFam.InterpFam.vFam_interp | (intros; apply GlobalTheory.MetFam.InterpFam.vFam_interp <;> assumption)
