import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

variable {A B R : Type} [CommRing A] [CommRing B] [CommRing R]

def IsRingHomMod (π : B →+* A) (β : B →+* R) (n : ℕ) (φ : A → PowerSeries R) : Prop :=
  (∀ f g, (X : PowerSeries R) ^ n ∣ φ (f * g) - φ f * φ g) ∧
  (∀ f g, (X : PowerSeries R) ^ n ∣ φ (f + g) - (φ f + φ g)) ∧
  (X : PowerSeries R) ^ n ∣ φ 1 - 1 ∧
  (∀ b, (X : PowerSeries R) ^ n ∣ φ (π b) - C (β b))

def IsJet (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (n : ℕ)
    (φ : A → PowerSeries R) : Prop :=
  IsRingHomMod π β n φ ∧
  (∀ f, (X : PowerSeries R) ^ n ∣ φ (m f) - rescale 2 (φ f)) ∧
  (∀ f, constantCoeff (φ f) = β (ε f)) ∧
  (∀ f, coeff 1 (φ f) = δ f)

theorem deriv_comp_m (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (E : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (hE : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f) (hEπ : ∀ a, E (π a) = 0) (f : A) :
    E (m f) = 2 * E f := by
  have hsq : ∀ x ∈ RingHom.ker ε ^ 2, E x = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [RingHom.mem_ker] at ha hb
      rw [hE, ha, hb]; simp
    · rw [map_add, ha, hb, add_zero]
  have hk : f - π (ε f) ∈ RingHom.ker ε := by
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply ε π, hεπ, RingHom.id_apply, sub_self]
  have h1 : m f = π (ε f) + (m (f - π (ε f)) - 2 * (f - π (ε f))) + (f - π (ε f)) + (f - π (ε f)) := by
    have : m (π (ε f)) = π (ε f) := by rw [← RingHom.comp_apply m π, hmπ]
    rw [map_sub, this]; ring
  have h2 : f = π (ε f) + (f - π (ε f)) := by ring
  rw [h1, map_add, map_add, map_add, hEπ, hsq _ (hm2 _ hk)]
  conv_rhs => rw [h2, map_add, hEπ]
  ring

end GlobalTheory.Nef.PathJet
