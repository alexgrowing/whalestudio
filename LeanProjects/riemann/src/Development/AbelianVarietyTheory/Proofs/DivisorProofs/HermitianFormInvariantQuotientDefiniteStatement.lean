import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormInvariantQuotientDefinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_invariant_quotient_definite : ∀ {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] (ρ : G →* Module.End ℂ V)
    (𝒦 : Set (Subgroup G)) (B : V → V → ℂ) (D N : Submodule ℂ V)
    (hD : ∀ g, ∀ x ∈ D, ρ g x ∈ D) (hND : N ≤ D) (hne : N ≠ D) (hN : ∀ g, ∀ x ∈ N, ρ g x ∈ N)
    (hadd : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z)
    (hsmul : ∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y)
    (hherm : ∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y))
    (hpos : ∀ x ∈ D, 0 ≤ (B x x).re)
    (hinv : ∀ g, ∀ x ∈ D, ∀ y ∈ D, B (ρ g x) (ρ g y) = B x y)
    (hrad : ∀ x ∈ D, B x x = 0 → x ∈ N)
    (hsm : ∀ x ∈ D, ∃ K ∈ 𝒦, ∀ k ∈ K, ρ k x = x)
    (hfin : ∀ K ∈ 𝒦, ∀ x ∈ D, {y | ∃ k ∈ K, ρ k x = y}.Finite)
    (hadm : ∀ K ∈ 𝒦, ∀ x ∈ D, ∃ s : Finset V, (↑s ⊆ (D : Set V)) ∧
      ∀ y ∈ Submodule.span ℂ (Set.range fun g => ρ g x), (∀ k ∈ K, ρ k y = y) →
        ∃ z ∈ Submodule.span ℂ (s : Set V), B (y - z) (y - z) = 0),
    ∃ S : Submodule ℂ V, S ≤ D ∧ GlobalTheory.ThKLocSS.IsSimpleOver (Set.range ρ) N S := by
  first | exact @GlobalTheory.UnitaryRep.exists_isSimpleOver_of_unitary | exact GlobalTheory.UnitaryRep.exists_isSimpleOver_of_unitary | (intros; apply GlobalTheory.UnitaryRep.exists_isSimpleOver_of_unitary <;> assumption)
