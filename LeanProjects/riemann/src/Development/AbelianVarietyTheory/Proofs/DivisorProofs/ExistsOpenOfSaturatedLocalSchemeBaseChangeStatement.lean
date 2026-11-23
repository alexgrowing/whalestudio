import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenOfSaturatedLocalSchemeBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_of_saturated_local_scheme_baseChange : ∀ (S S₁ P : Scheme.{0}) (p : P ⟶ S) (x : S) (ξ' : S₁ ⟶ Spec (S.presheaf.stalk x)) (ξ : S₁ ⟶ S), ξ' ≫ S.fromSpecStalk x = ξ → Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ O : Set ↥(Limits.pullback p ξ), IsOpen O → (∀ w w' : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w = Limits.pullback.fst p ξ w' → w ∈ O → w' ∈ O) → ∃ V : P.Opens, ∀ w : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w ∈ V ↔ w ∈ O := by
  first | exact @GlobalTheory.Desc.exists_open_of_saturated_stalkBaseChange | exact GlobalTheory.Desc.exists_open_of_saturated_stalkBaseChange | (intros; apply GlobalTheory.Desc.exists_open_of_saturated_stalkBaseChange <;> assumption)
