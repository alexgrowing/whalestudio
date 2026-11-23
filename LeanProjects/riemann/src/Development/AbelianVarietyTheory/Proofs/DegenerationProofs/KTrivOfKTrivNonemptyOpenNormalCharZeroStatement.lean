import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_of_kTriv_nonemptyOpen_normal_charZero : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → (∀ n : ℕ, n ≠ 0 → (n : Γ(S, ⊤)) ≠ 0) → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L), IsAbelianScheme G → Out.RelAmple G L.L → Out.KTriv ((Over.pullback U.ι).obj G) (L.L.pull (pullback.fst G.hom U.ι)) → Out.KTriv G L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_open_normal | exact GlobalTheory.KTrivSpread.kTriv_of_open_normal | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_open_normal <;> assumption)
