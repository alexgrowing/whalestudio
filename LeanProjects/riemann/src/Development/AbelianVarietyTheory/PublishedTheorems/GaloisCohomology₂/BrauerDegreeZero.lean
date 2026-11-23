import Mathlib

noncomputable section

namespace GlobalTheory.Published

open Classical in

def indFun {G : Type} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ x : G, if hx : x⁻¹ * g * x ∈ H then f ⟨x⁻¹ * g * x, hx⟩ else 0

def BrauerDegreeZero : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V),
    ∃ (r : ℕ) (H : Fin r → Subgroup G) (χ : ∀ i, H i →* ℂˣ) (c : Fin r → ℤ), ∀ g : G,
      LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ) =
        ∑ i, (c i : ℂ) * (indFun (H i) (fun x => (χ i x : ℂ)) g - indFun (H i) (fun _ => 1) g)

end GlobalTheory.Published

end
