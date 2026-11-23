import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero

namespace GlobalTheory.DZA.OrbSupp

open GlobalTheory.BCT

variable {G : Type} [Group G] [TopologicalSpace G]

theorem exists_twConj_ne_zero (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) :
    ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold twOrb
  simp only [hc]
  simp [avg]

theorem twOrb_eq_zero_of_forall (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (h : ∀ x, f (x⁻¹ * δ * θ x) = 0) : twOrb θ K δ f = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := exists_twConj_ne_zero θ K δ f hne
  exact hx (h x)

theorem exists_conj_ne_zero (K : Subgroup G) (γ : G) (f : G → ℂ) (h : twOrb (MonoidHom.id G) K γ f ≠ 0) :
    ∃ x, f (x⁻¹ * γ * x) ≠ 0 :=
  exists_twConj_ne_zero (MonoidHom.id G) K γ f h

theorem twOrb_id_eq_zero_of_forall (K : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    twOrb (MonoidHom.id G) K γ f = 0 :=
  twOrb_eq_zero_of_forall (MonoidHom.id G) K γ f h

example (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) :
    ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := exists_ne_zero_of_twOrb_ne_zero θ K δ f h

end GlobalTheory.DZA.OrbSupp
