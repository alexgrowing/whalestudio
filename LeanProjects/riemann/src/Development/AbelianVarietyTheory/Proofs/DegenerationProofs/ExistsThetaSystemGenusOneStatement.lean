import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemGenusOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_system_genus_one : Laws → Laws2 → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω), S.g = 1 ∧ S.Big ∧ Nonempty S.Real := by
  first | exact @GlobalTheory.ZH.RealDimOne.exists_real_dim_one | exact GlobalTheory.ZH.RealDimOne.exists_real_dim_one | (intros; apply GlobalTheory.ZH.RealDimOne.exists_real_dim_one <;> assumption)
