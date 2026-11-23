import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyGeometricSpecialFibreUniformisedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GoodReductionAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesAtPointIntegralOfPeriodValuationStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem utest_nonempty_mod : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → Nonempty (Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hb
  obtain ⟨-, hdim, hsm, h4, -⟩ := utest_dim_and_split hL o Ω S ρ p y₀ u
  have h1 : 1 ≤ S.N := le_trans (by norm_num) h4
  obtain ⟨fb⟩ := GlobalTheory.T.nonempty_geometric_special_fibre_uniformised hL o Ω S ρ p y₀ u S.N h1
  obtain ⟨F, hF, hred⟩ := fb.exp S.J σ f (fun i => hb.2.2.2.1 i 0)
  refine ⟨{ isLB := LB.isLB_linComb u.U.LG.isLB _ _
            smooth := hsm
            Φ := fb.Φ
            r := fb.r
            cart := fb.cart
            xe := fb.xe
            F := F
            good := GlobalTheory.T.good_reduction_adapted_basis hL o Ω S ρ p y₀ u l S.N fb h1 S.J σ cls f hb F hF
            pol := fb.pol
            dim := ?_
            red := hred
            ser := GlobalTheory.T.theta_series_at_point_integral_of_period_valuation hL hT o Ω S ρ p y₀ u l σ cls f hb }⟩
  rw [fb.dim, fb.xe.toIntLinearEquiv.finrank_eq]
  exact hdim

end GlobalTheory.ZH
