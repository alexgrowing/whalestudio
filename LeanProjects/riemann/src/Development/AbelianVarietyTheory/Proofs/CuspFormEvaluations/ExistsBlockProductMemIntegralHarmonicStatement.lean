import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBlockProductMemIntegralHarmonic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockProduct_mem_integralHarmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ i k, i ≤ k → a (τ, k) ≤ a (τ, i)) → I2.PT.f E * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * n → ∃ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA c a n ∧ IsBlockProd P ∧ P.totalDegree = Formalism.L2.Pj.DF Dw a ∧ ∀ σ : c.F →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) ^ Formalism.L2.Pj.DF Dw a := by
  first | exact @GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA | exact GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA | (intros; apply GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA <;> assumption)
