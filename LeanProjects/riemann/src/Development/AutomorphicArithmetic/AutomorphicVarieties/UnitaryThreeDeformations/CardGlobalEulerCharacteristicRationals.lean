import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

theorem UpperTheory.card_global_euler_characteristic_rationals :
    GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (ρ : Representation (ZMod (l ^ 1)) (Gam Ω S) M),
            ContainsAbove S l → ContAction ρ → ∀ σ : Formalism.ConjugateSelfDual.G ℚ Ω, IsCC σ →
            Nat.card (H1 ρ) * Nat.card {m : M // ρ (toGS Ω _ σ) m = m} = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M := by
  intro hG Ω _ _ _ l _ _ M _ _ _ _ _ S ρ hS hρ σ hσ
  have h := hG ℚ Ω l 1 M S ρ Nat.one_pos hS hρ (fun _ => σ) (by
    intro w _
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, hj, Subsingleton.elim _ _⟩)
  have hc : NumberField.InfinitePlace.nrComplexPlaces ℚ = 0 :=
    NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  simp only [archH0Card, hc, pow_zero, mul_one, Module.finrank_self, pow_one] at h
  rw [Finset.prod_eq_single_of_mem Rat.infinitePlace
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Rat.isReal_infinitePlace)
    (fun b _ hb => absurd (Subsingleton.elim b _) hb)] at h
  exact h.symm
