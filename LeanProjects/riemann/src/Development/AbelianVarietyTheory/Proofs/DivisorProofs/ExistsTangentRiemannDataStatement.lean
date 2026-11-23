import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentRiemannData
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
theorem _root_.GlobalTheory.T.exists_tangent_riemann_data : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (Q : Out.PolAV T) (θ : Q.A.left ⟶ s.T.Z.t.G.left), IsGrpPullback Q.A s.T.Z.t.G b θ → ∀ (y₀ : Sp ℂ ⟶ T) (d : (PPAS.ofPolAV Q).RiemannData y₀) (v₀ : Sp (DualNumber ℂ) ⟶ s.T.Z.t.G.left), Formalism.L2.Pj.IsTanAtG s.T.Z.t (y₀ ≫ b) v₀ → ∃ (w : Fin Q.g → ℂ) (v : epsR ℂ ⟶ d.B), IsTangent v ∧ d.u.IsDiff w v ∧ v.left ≫ d.φ ≫ θ = v₀ := by
  first | exact @GlobalTheory.TanLift.exists_lift | exact GlobalTheory.TanLift.exists_lift | (intros; apply GlobalTheory.TanLift.exists_lift <;> assumption)
