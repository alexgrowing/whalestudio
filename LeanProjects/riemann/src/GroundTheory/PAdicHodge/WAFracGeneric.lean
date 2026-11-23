import Mathlib
import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open ACris

namespace WAFrac

variable {p : ℕ} [hp : Fact p.Prime]

section Frac

variable {G R : Type*} [CommRing R] [IsDomain R] [Algebra ℚ_[p] R]

theorem le_comap_of_injective (f : R →+* R) (hf : Function.Injective f) :
    nonZeroDivisors R ≤ (nonZeroDivisors R).comap f := fun x hx =>
  mem_nonZeroDivisors_of_ne_zero fun h : f x = 0 =>
    nonZeroDivisors.ne_zero hx (hf (show f x = f 0 by rw [h, map_zero]))

def fracMap (f : R →+* R) (hf : Function.Injective f) : FractionRing R →+* FractionRing R :=
  IsLocalization.map (S := FractionRing R) (FractionRing R) f (le_comap_of_injective f hf)

theorem fracMap_algebraMap (f : R →+* R) (hf : Function.Injective f) (x : R) :
    fracMap f hf (algebraMap R (FractionRing R) x) = algebraMap R (FractionRing R) (f x) :=
  IsLocalization.map_eq (S := FractionRing R) (le_comap_of_injective f hf) x

theorem fracMap_comp (f₁ f₂ : R →+* R) (h₁ : Function.Injective f₁) (h₂ : Function.Injective f₂)
    (h : ∀ x, f₁ (f₂ x) = f₂ (f₁ x)) (y : FractionRing R) :
    fracMap f₁ h₁ (fracMap f₂ h₂ y) = fracMap f₂ h₂ (fracMap f₁ h₁ y) := by
  have e : (fracMap f₁ h₁).comp (fracMap f₂ h₂) = (fracMap f₂ h₂).comp (fracMap f₁ h₁) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, fracMap_algebraMap, h])
  exact congrArg (fun F : FractionRing R →+* FractionRing R => F y) e

theorem fracMap_iterate (f : R →+* R) (hf : Function.Injective f) (n : ℕ) (x : R) :
    (fracMap f hf)^[n] (algebraMap R (FractionRing R) x) = algebraMap R (FractionRing R) (f^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, fracMap_algebraMap, Function.iterate_succ_apply']

theorem exists_pair_phi (φ : R →+* R) (hφ : Function.Injective φ)
    (hφq : ∀ q : ℚ_[p], φ (algebraMap ℚ_[p] R q) = algebraMap ℚ_[p] R q)
    (g : G → R →+* R) (hg : ∀ σ, Function.Injective (g σ))
    (hgq : ∀ σ (q : ℚ_[p]), g σ (algebraMap ℚ_[p] R q) = algebraMap ℚ_[p] R q)
    (hgφ : ∀ σ x, g σ (φ x) = φ (g σ x)) {t : R} (ht : φ t = (p : R) * t)
    (hper : ∀ x : R, (∀ σ, g σ x = x) → ∃ n d, 0 < d ∧ φ^[n + d] x = φ^[n] x)
    (hfix : ∀ x y : R, y ≠ 0 → (∀ σ, g σ x * y = x * g σ y) → ∃ z : R, (∀ σ, g σ z = z) ∧ x = z * y)
    (c : G → ℚ_[p]) {a b : R} (hb : b ≠ 0)
    (hrel : ∀ σ, g σ a * b - a * g σ b = algebraMap ℚ_[p] R (c σ) * t * g σ b * b) :
    ∃ a' b' : R, b' ≠ 0 ∧ φ a' * b' = (p : R) * a' * φ b' ∧
      ∀ σ, g σ a' * b' - a' * g σ b' = algebraMap ℚ_[p] R (c σ) * t * g σ b' * b' := by
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hne : ∀ {x : R}, x ≠ 0 → algebraMap R (FractionRing R) x ≠ 0 := fun hx h =>
    hx (hinj (by rw [h, map_zero]))
  have hιq : ∀ q : ℚ_[p], algebraMap ℚ_[p] (FractionRing R) q =
      algebraMap R (FractionRing R) (algebraMap ℚ_[p] R q) := fun q =>
    IsScalarTower.algebraMap_apply ℚ_[p] R (FractionRing R) q
  have hgz : ∀ σ {z : R}, z ≠ 0 → g σ z ≠ 0 := fun σ z hz h => hz (hg σ (by rw [h, map_zero]))

  have hy : ∀ σ, fracMap (g σ) (hg σ) (algebraMap R _ a / algebraMap R _ b) -
      algebraMap R _ a / algebraMap R _ b = algebraMap ℚ_[p] (FractionRing R) (c σ) * algebraMap R _ t := by
    intro σ
    rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hιq, div_sub_div _ _ (hne (hgz σ hb)) (hne hb),
      div_eq_iff (mul_ne_zero (hne (hgz σ hb)) (hne hb))]
    have h := congrArg (algebraMap R (FractionRing R)) (hrel σ)
    simp only [map_sub, map_mul] at h
    linear_combination h

  have hperF : ∀ μ : FractionRing R, (∀ σ, fracMap (g σ) (hg σ) μ = μ) →
      ∃ n d, 0 < d ∧ (fracMap φ hφ)^[n + d] μ = (fracMap φ hφ)^[n] μ := by
    intro μ hμ
    obtain ⟨x, z, hz, rfl⟩ := IsFractionRing.div_surjective (A := R) μ
    have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
    have hcross : ∀ σ, g σ x * z = x * g σ z := by
      intro σ
      have h1 := hμ σ
      rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, div_eq_div_iff (hne (hgz σ hz0)) (hne hz0)]
        at h1
      apply hinj
      simp only [map_mul]
      exact h1
    obtain ⟨w, hw, rfl⟩ := hfix x z hz0 hcross
    obtain ⟨n, d, hd, hnd⟩ := hper w hw
    refine ⟨n, d, hd, ?_⟩
    have e : algebraMap R (FractionRing R) (w * z) / algebraMap R _ z = algebraMap R _ w := by
      rw [map_mul, mul_div_assoc, div_self (hne hz0), mul_one]
    rw [e, fracMap_iterate, fracMap_iterate, hnd]
  obtain ⟨y', hφy', hgy'⟩ := exists_eq_p_mul_of_sub_eq (fracMap φ hφ)
    (fun q => by rw [hιq, fracMap_algebraMap, hφq]) (fun σ => fracMap (g σ) (hg σ))
    (fun σ q => by rw [hιq, fracMap_algebraMap, hgq])
    (fun σ x => fracMap_comp _ _ _ _ (fun x => hgφ σ x) x)
    (show fracMap φ hφ (algebraMap R _ t) = (p : FractionRing R) * algebraMap R _ t by
      rw [fracMap_algebraMap, ht, map_mul, map_natCast])
    hperF c hy

  obtain ⟨a', b', hb', rfl⟩ := IsFractionRing.div_surjective (A := R) y'
  have hb'0 : b' ≠ 0 := nonZeroDivisors.ne_zero hb'
  have hφb' : φ b' ≠ 0 := fun h => hb'0 (hφ (by rw [h, map_zero]))
  refine ⟨a', b', hb'0, ?_, fun σ => ?_⟩
  · rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, mul_div_assoc', div_eq_div_iff (hne hφb') (hne hb'0)]
      at hφy'
    apply hinj
    simp only [map_mul, map_natCast]
    linear_combination hφy'
  · have h1 := hgy' σ
    rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hιq, div_sub_div _ _ (hne (hgz σ hb'0)) (hne hb'0),
      div_eq_iff (mul_ne_zero (hne (hgz σ hb'0)) (hne hb'0))] at h1
    apply hinj
    simp only [map_mul, map_sub]
    linear_combination h1

end Frac

section Away

variable {G R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem exists_common_den (t : R) [IsLocalization.Away t S] (x y : S) : ∃ (n : ℕ) (α β : R),
    x * algebraMap R S (t ^ n) = algebraMap R S α ∧ y * algebraMap R S (t ^ n) = algebraMap R S β := by
  obtain ⟨n₁, α₁, h₁⟩ := IsLocalization.Away.surj t x
  obtain ⟨n₂, β₂, h₂⟩ := IsLocalization.Away.surj t y
  refine ⟨n₁ + n₂, α₁ * t ^ n₂, β₂ * t ^ n₁, ?_, ?_⟩
  · rw [pow_add, map_mul, ← mul_assoc, map_pow, h₁, map_mul]
  · rw [pow_add, mul_comm (t ^ n₁), map_mul, ← mul_assoc, map_pow, h₂, map_mul]

theorem exists_pair_away (t : R) [IsLocalization.Away t S] (hinj : Function.Injective (algebraMap R S)) (φR : R →+* R) (φS : S →+* S)
    (hφ : ∀ x, φS (algebraMap R S x) = algebraMap R S (φR x)) (gR : G → R →+* R) (gS : G → S →+* S)
    (hg : ∀ σ x, gS σ (algebraMap R S x) = algebraMap R S (gR σ x)) (T : G → R) {a b : S}
    (hb : b ≠ 0) (hφab : φS a * b = (p : S) * a * φS b)
    (hgab : ∀ σ, gS σ a * b - a * gS σ b = algebraMap R S (T σ) * gS σ b * b) :
    ∃ α β : R, β ≠ 0 ∧ φR α * β = (p : R) * α * φR β ∧
      ∀ σ, gR σ α * β - α * gR σ β = T σ * gR σ β * β := by
  obtain ⟨n, α, β, ha, hb'⟩ := exists_common_den t a b
  have hu : IsUnit (algebraMap R S (t ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit t).pow n
  refine ⟨α, β, ?_, ?_, fun σ => ?_⟩
  · rintro rfl
    rw [map_zero] at hb'
    exact hb (hu.mul_left_eq_zero.1 hb')
  · apply hinj
    have hφa := congrArg φS ha
    have hφb := congrArg φS hb'
    simp only [map_mul, hφ] at hφa hφb
    simp only [map_mul, map_natCast]
    rw [← hφa, ← hb', ← ha, ← hφb]
    linear_combination (algebraMap R S (φR (t ^ n)) * algebraMap R S (t ^ n)) * hφab
  · apply hinj
    have hga := congrArg (gS σ) ha
    have hgb := congrArg (gS σ) hb'
    simp only [map_mul, hg] at hga hgb
    simp only [map_mul, map_sub]
    rw [← hga, ← hb', ← ha, ← hgb]
    linear_combination (algebraMap R S (gR σ (t ^ n)) * algebraMap R S (t ^ n)) * hgab σ

end Away

end WAFrac

end GroundTheory.PAdicHodge
