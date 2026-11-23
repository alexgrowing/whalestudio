import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumStabilizerWeightedPairOrbitsConjClass
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    ∀ γ₀ : Γ, ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  first | (exact @GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (exact GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (intros; apply GlobalTheory.MassConj.finsum_pairOrbit_fibre  <;> assumption)
