import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_eq_of_similitude_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.Rel Q → Q.term Kf f r K φ = P.term Kf f r K φ := by
  first | (exact @GlobalTheory.LKMid.Pair.term_eq_of_rel) | (exact GlobalTheory.LKMid.Pair.term_eq_of_rel) | (intros; apply GlobalTheory.LKMid.Pair.term_eq_of_rel <;> assumption)
