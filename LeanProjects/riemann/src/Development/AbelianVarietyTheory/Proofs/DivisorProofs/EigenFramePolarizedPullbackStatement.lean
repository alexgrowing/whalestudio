import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFramePolarizedPullback
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
theorem _root_.GlobalTheory.T.eigen_frame_polarized_pullback : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (Q : Out.PolAV T) (θ : Q.A.left ⟶ s.T.Z.t.G.left), IsGrpPullback Q.A s.T.Z.t.G b θ → LBIso (s.T.Z.t.PP.L.pull θ) Q.L → ∀ (σ' : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ' → ∀ (yc : CxPts (genStr s.T.Z) σ') (y₀ : Sp ℂ ⟶ T), y₀ ≫ b = yc.1 ≫ genι s.T.Z → ∀ (u : EigFrame s.T.Z σ' (yc.1 ≫ genι s.T.Z)) (d : (PPAS.ofPolAV Q).RiemannData y₀) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → Fin Q.g → ℂ), (∀ τ i, ∃ v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff (z τ i) v ∧ v.left ≫ d.φ ≫ θ = u.v τ i) → (∀ τ b₁ b₂, (x.hodge σ').gram yc u τ b₁ b₂ = (Real.pi : ℂ) * hermForm d.H (z τ b₂) (z τ b₁)) ∧ ∀ τ τ' b₁ b₂, τ ≠ τ' → hermForm d.H (z τ b₁) (z τ' b₂) = 0 := by
  first | exact @GlobalTheory.HodgeRiemFibre.hodge_gram_eq | exact GlobalTheory.HodgeRiemFibre.hodge_gram_eq | (intros; apply GlobalTheory.HodgeRiemFibre.hodge_gram_eq <;> assumption)
