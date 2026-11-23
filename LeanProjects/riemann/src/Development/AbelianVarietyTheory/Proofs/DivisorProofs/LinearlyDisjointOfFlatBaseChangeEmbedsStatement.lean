import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointOfFlatBaseChangeEmbeds
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearlyDisjoint_of_flat_baseChange_embeds : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → LinDisj (algebraMap R K) c θ := by
  first | exact @GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat | exact GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat | (intros; apply GlobalTheory.Desc.FlatLinDisj.linDisj_of_flat <;> assumption)
