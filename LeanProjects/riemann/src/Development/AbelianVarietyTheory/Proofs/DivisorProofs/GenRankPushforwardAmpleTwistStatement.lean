import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenRankPushforwardAmpleTwist
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
theorem _root_.GlobalTheory.T.gen_rank_pushforward_ample_twist : ∀ (k : Type) [Field k] (T T' : Scheme.{0}) [Algebra k Γ(T, ⊤)] [Algebra k Γ(T', ⊤)] [IsIntegral T] [IsIntegral T'], IsProjSurface k T → IsProjSurface k T' → ∀ (ρ : T' ⟶ T), ρ ≫ strHom k T = strHom k T' → ∀ (d : ℕ), IsGenFinite ρ d → ∀ (M : LB T'), M.IsLB → genRank ((Scheme.Modules.pushforward ρ).obj (twist (structureModule T') M)) = d := by
  first | exact @GlobalTheory.PushGenRank.genRank_pushforward_twist | exact GlobalTheory.PushGenRank.genRank_pushforward_twist | (intros; apply GlobalTheory.PushGenRank.genRank_pushforward_twist <;> assumption)
