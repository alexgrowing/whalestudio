import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialLatticeEndomorphismLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLatticeSpans
open scoped TensorProduct NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_lattice_endomorphism_lift : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) → Module.Finite ℤ L →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    Module.Free ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) → Module.Finite ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    Module.finrank ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) = Fintype.card κ * Module.finrank ℚ E →
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M,
      ∀ (a : 𝓞 E) (r : κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E), f (((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) • r) = α a (f r) := by
  first | exact @GlobalTheory.TorusTateFree.tate_free_of_lattice | exact GlobalTheory.TorusTateFree.tate_free_of_lattice | (intros; apply GlobalTheory.TorusTateFree.tate_free_of_lattice <;> assumption)
