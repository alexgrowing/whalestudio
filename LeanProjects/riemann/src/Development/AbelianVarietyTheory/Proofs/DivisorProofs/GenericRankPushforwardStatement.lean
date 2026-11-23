import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRankPushforward
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_rank_pushforward : ∀ (T T' : Scheme.{0}) [IsIntegral T] [IsIntegral T'] (ρ : T' ⟶ T) (h : ρ (genericPoint T') ⤳ genericPoint T), (∀ V : T'.Opens, genericPoint T' ∈ V → ∃ U : T.Opens, genericPoint T ∈ U ∧ ρ ⁻¹ᵁ U ≤ V) → ∀ F : T'.Modules, genRank ((Scheme.Modules.pushforward ρ).obj F) = (letI := (T.presheaf.stalkSpecializes h ≫ ρ.stalkMap (genericPoint T')).hom.toAlgebra; Module.finrank T.functionField T'.functionField) * genRank F := by
  first | exact @GlobalTheory.VB.genRank_pushforward_of_generic | exact GlobalTheory.VB.genRank_pushforward_of_generic | (intros; apply GlobalTheory.VB.genRank_pushforward_of_generic <;> assumption)
