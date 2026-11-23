import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorDecompositionFlagSteps
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_decomposition_flag_steps : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (μ : Fin N → ℤ), StrictAnti μ → ∃ (w : GlobalTheory.FlagAmple.Step S.Dw → ℕ) (c : (D.host.E →+* ℂ) → ℤ), (∀ x, 0 < w x) ∧ -∑ x : DV.Rt D.what₂.Tau N, μ x.2 • divOf (Φ.C k) (rootEx S.Dw (DV.tauEmb D x.1) x.2) = ∑ x : GlobalTheory.FlagAmple.Step S.Dw, (w x : ℤ) • -GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ) + ∑ τ : D.host.E →+* ℂ, c τ • GlobalTheory.FlagAmple.detDiv (Φ.C k) τ (S.Dw.mult τ) := by
  first | exact @GlobalTheory.FlagAmple.BorelWeil.lmu_div_eq | exact GlobalTheory.FlagAmple.BorelWeil.lmu_div_eq | (intros; apply GlobalTheory.FlagAmple.BorelWeil.lmu_div_eq <;> assumption)
