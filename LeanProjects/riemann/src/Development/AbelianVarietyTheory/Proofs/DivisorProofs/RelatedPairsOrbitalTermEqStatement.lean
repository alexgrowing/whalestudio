import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsOrbitalTermEq
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.related_pairs_orbital_term_eq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Q Q' : DPair G), Q.Rel Q' → Q.pol = Q'.pol ∧ Q.c = Q'.c ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → Q.term Kf f r K φ = Q'.term Kf f r K φ := by
  first | exact @GlobalTheory.LKDef.DPair.rel_pol_c_term | exact GlobalTheory.LKDef.DPair.rel_pol_c_term | (intros; apply GlobalTheory.LKDef.DPair.rel_pol_c_term <;> assumption)
