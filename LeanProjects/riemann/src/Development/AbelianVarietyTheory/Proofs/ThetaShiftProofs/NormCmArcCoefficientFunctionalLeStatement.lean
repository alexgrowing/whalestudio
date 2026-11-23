import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormCmArcCoefficientFunctionalLe
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_cmArcCoefficientFunctional_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (xi S : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → 1 ≤ La → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = xi) → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, 0 ≤ S → (∀ k, ∀ y ∈ (U.X k).dom, lieFac Dw xi a' * (U.X k).pnorm (laU U a' n k) (rdU U F k) y ≤ S) → ‖em (cfOf d.yF d.μ d.jj F)‖ * (s.valLine d.μ n).n em ≤ S * Real.exp (4 * Real.pi + GlobalTheory.ArcCM.archP E r La c₁ * ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n)) := by
  first | exact @GlobalTheory.ArchCM.norm_cfOf_le | exact GlobalTheory.ArchCM.norm_cfOf_le | (intros; apply GlobalTheory.ArchCM.norm_cfOf_le <;> assumption)
