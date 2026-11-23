import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetricLift_action_geometricFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a)).left → x ^ S.N = 1 → ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)), SymLift u.A.A u.A.L S.N S.N x θ ∧ ∀ i t', IsActOf u.A.A u.A.L S.N θ (t i) t' → SecM.ofSec u.A.A t' = ∑ l, kf u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a l i))) • SecM.ofSec u.A.A (t l) := by
  first | exact @GlobalTheory.ZH.ClassWeight.exists_symLift_act | exact GlobalTheory.ZH.ClassWeight.exists_symLift_act | (intros; apply GlobalTheory.ZH.ClassWeight.exists_symLift_act <;> assumption)
