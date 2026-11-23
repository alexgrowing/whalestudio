import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePowerIsoMinimalSiegelCompactification
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_power_iso_minimalSiegelCompactification : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), MinAt5 F z i OZ → IsNormalScheme S → IsProjOver (π ≫ z) → Dense (Set.range j) → j ≫ π = i → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsGrpPullback F.univ.A G j e → ∃ a N : ℕ, 1 ≤ a ∧ 1 ≤ N ∧ LBIso (lbPow (hodge G g) N) (lbPow (OZ.pull π) a) := by
  first | exact @GlobalTheory.HodgeMin.hodge_pow_iso_pull_pow_of_minimal_compactification | exact GlobalTheory.HodgeMin.hodge_pow_iso_pull_pow_of_minimal_compactification | (intros; apply GlobalTheory.HodgeMin.hodge_pow_iso_pull_pow_of_minimal_compactification <;> assumption)
