import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogChartLinearIndependent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_chart_linear_independent : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (n g r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps s.T.Z σ g) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), IsLogChart k ch ex lam ρ → ∃ M : Matrix (Fin r) (Fin r) ℝ, ∀ t ∈ logDom n k, LinearIndependent ℝ (lam t) ∧ Submodule.span ℝ (Set.range (lam t)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) ∧ (∀ i i', (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam t i) (lam t i')).im = M i i') ∧ ∀ (f : EigFrame s.T.Z σ ((ch.symm (logExp k t)).1 ≫ genι s.T.Z)) (W : Letter S.Dw → Fin g → ℂ), Dirs (Z := s.T.Z) ⟨ch.symm (logExp k t), f⟩ (fun w => (ex (ch.symm (logExp k t)) w).left) W → ∀ τ : D.host.E →+* ℂ, (x.hodge σ).gram (ch.symm (logExp k t)) f τ = (Real.pi : ℂ) • Matrix.of fun b b' => ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (W ⟨τ, b'⟩) (W ⟨τ, b⟩) := by
  first | exact @GlobalTheory.ShFam.Hor.HodgeLoc.hodge_eq_riem_chart | exact GlobalTheory.ShFam.Hor.HodgeLoc.hodge_eq_riem_chart | (intros; apply GlobalTheory.ShFam.Hor.HodgeLoc.hodge_eq_riem_chart <;> assumption)
