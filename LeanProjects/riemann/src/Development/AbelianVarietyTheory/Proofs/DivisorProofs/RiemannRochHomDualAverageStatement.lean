import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRochHomDualAverage
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_roch_hom_dual_average : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E r → ∀ (F : T.Modules), QCoh.IsFiniteQC F → ((chi k (homMod (dual E) F) : ℚ) + (chi k (homMod E F) : ℚ)) / 2 - (r : ℚ) * (chi k F : ℚ) = (genRank F : ℚ) * degCh2 k E := by
  first | exact @GlobalTheory.RRDev.psi_eq_genRank_mul_degCh2 | exact GlobalTheory.RRDev.psi_eq_genRank_mul_degCh2 | (intros; apply GlobalTheory.RRDev.psi_eq_genRank_mul_degCh2 <;> assumption)
