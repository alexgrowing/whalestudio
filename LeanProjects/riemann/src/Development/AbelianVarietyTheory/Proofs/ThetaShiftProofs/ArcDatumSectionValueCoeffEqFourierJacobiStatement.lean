import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ToroidalArchimedeanCondition → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (ξ : Module.Dual ℤ d.a.D₀.X) (ν₀ : E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c (ι.comp (algebraMap c.F K₁)) → IsUnf U → d.OverBase → (∀ τ k, GtTanR (d.e τ k)) → PushInvertible d.Y.t.G d.Y.t.PP.L → Module.finrank (𝓞 E) d.a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' d.a.be ν₀ d.jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∃ (k : U.Comp) (ξ' : Fin r → E) (fr : (ArcLt Dw → ℂ) → Frame (U.X k).Ψ r) (u₁ : ℂ) (κ : (ArcLt Dw → ℂ) → ℂ), u₁ ≠ 0 ∧ (U.X k).IsIso ξ' ∧ (∀ x, InvBl x → κ x ≠ 0) ∧ (∀ x, InvBl x → fr x ∈ (U.X k).dom) ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → ∀ x, InvBl x → ajAt d ι F x * u₁ ^ d.jj = κ x * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) (fr x) := by
  first | exact @GlobalTheory.ArcId.ajAt_eq_fj | exact GlobalTheory.ArcId.ajAt_eq_fj | (intros; apply GlobalTheory.ArcId.ajAt_eq_fj <;> assumption)
