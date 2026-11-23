import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem units_localization_descend_away (A : Type) [CommRing A] (M : Submonoid A)
    (u : (Localization M)ˣ) :
    ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M,
      φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  obtain ⟨⟨a, m₁⟩, ha⟩ := IsLocalization.mk'_surjective M (u : Localization M)
  obtain ⟨⟨b, m₂⟩, hb⟩ := IsLocalization.mk'_surjective M ((u⁻¹ : (Localization M)ˣ) : Localization M)
  simp only at ha hb
  have hprod : IsLocalization.mk' (Localization M) (a * b) (m₁ * m₂) = 1 := by
    rw [IsLocalization.mk'_mul, ha, hb]; simp
  have h1 : algebraMap A (Localization M) (a * b) = algebraMap A (Localization M) ((m₁ * m₂ : M) : A) := by
    have := IsLocalization.mk'_spec (Localization M) (a * b) (m₁ * m₂)
    rw [hprod, one_mul] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 h1
  set m : A := (m₁ : A) * m₂ * c with hm
  have hmM : m ∈ M := M.mul_mem (M.mul_mem m₁.2 m₂.2) c.2
  have hc' : (c : A) * (a * b) = (c : A) * ((m₁ : A) * m₂) := by
    simpa [Submonoid.coe_mul] using hc
  let s := IsLocalization.Away.invSelf (S := Localization.Away m) m
  have hs : algebraMap A (Localization.Away m) m * s = 1 := IsLocalization.Away.mul_invSelf m
  let x : Localization.Away m := algebraMap A _ (a * (m₂ * c)) * s
  let y : Localization.Away m := algebraMap A _ (b * (m₁ * c)) * s
  have hxy : x * y = 1 := by
    have e : a * (m₂ * c) * (b * (m₁ * c)) = m * m := by
      rw [hm]; linear_combination ((m₁ : A) * m₂ * c) * hc'
    calc x * y = algebraMap A _ (a * (m₂ * c) * (b * (m₁ * c))) * s * s := by
          simp only [x, y, map_mul]; ring
      _ = (algebraMap A (Localization.Away m) m * s) * (algebraMap A (Localization.Away m) m * s) := by
          rw [e, map_mul]; ring
      _ = 1 := by rw [hs, one_mul]
  refine ⟨m, hmM, ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  intro φ hφ
  have hφa : ∀ r : A, φ (algebraMap A _ r) = algebraMap A (Localization M) r := fun r =>
    congrArg (fun f : A →+* Localization M => f r) hφ
  apply Units.ext
  show φ x = (u : Localization M)
  have hu : (u : Localization M) * algebraMap A _ (m₁ : A) = algebraMap A _ a := by
    rw [← ha]; exact IsLocalization.mk'_spec _ _ _
  have hφs : algebraMap A (Localization M) m * φ s = 1 := by
    rw [← hφa, ← map_mul, hs, map_one]
  have hx : φ x * algebraMap A (Localization M) (m₁ : A) = algebraMap A _ a := by
    have : φ x * algebraMap A (Localization M) (m₁ : A)
        = algebraMap A (Localization M) a * (algebraMap A (Localization M) m * φ s) := by
      simp only [x, map_mul, hφa, hm]; ring
    rw [this, hφs, mul_one]
  have hunit : IsUnit (algebraMap A (Localization M) (m₁ : A)) := IsLocalization.map_units _ m₁
  exact hunit.mul_left_inj.1 (hx.trans hu.symm)

end GlobalTheory
