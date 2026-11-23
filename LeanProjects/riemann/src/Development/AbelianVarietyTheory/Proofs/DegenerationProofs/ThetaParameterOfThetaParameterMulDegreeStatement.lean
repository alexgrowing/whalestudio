import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaParameterOfThetaParameterMulDegree
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaParameter_of_thetaParameter_mul_degree : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N k : ℕ) (a : u.PtC) (g : GtPtF u.D.toPre (PadicAlgCl p)), 4 ≤ N → 1 ≤ k → u.ParAt (N * k) a g → u.ParAt N a g := by
  first | exact @GlobalTheory.ParameterRoot.parAt_of_parAt_mul | exact GlobalTheory.ParameterRoot.parAt_of_parAt_mul | (intros; apply GlobalTheory.ParameterRoot.parAt_of_parAt_mul <;> assumption)
