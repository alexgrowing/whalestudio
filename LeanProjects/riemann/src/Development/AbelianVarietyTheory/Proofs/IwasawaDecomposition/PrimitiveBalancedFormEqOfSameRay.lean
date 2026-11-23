import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem balForms_zsmul_cancel {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {g : ℤ} (hg : g ≠ 0) {a b : balForms bar X} (h : g • a = g • b) : a = b := by
  apply Subtype.ext
  refine LinearMap.ext₂ fun y z => ?_
  have h2 := LinearMap.congr_fun₂ (congrArg Subtype.val h) y z
  simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact mul_left_cancel₀ hg h2

theorem isPrim_ray_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  intro O _ bar X _ _ β β' p r hβ hβ' hp hr h
  set g := Nat.gcd p r with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hp
  obtain ⟨p₁, hp₁⟩ : g ∣ p := Nat.gcd_dvd_left p r
  obtain ⟨r₁, hr₁⟩ : g ∣ r := Nat.gcd_dvd_right p r
  have hcop : Nat.Coprime p₁ r₁ := by
    have := Nat.coprime_div_gcd_div_gcd (m := p) (n := r) hg
    rw [← hgdef] at this
    have e1 : p / g = p₁ := by rw [hp₁, Nat.mul_div_cancel_left _ hg]
    have e2 : r / g = r₁ := by rw [hr₁, Nat.mul_div_cancel_left _ hg]
    rwa [e1, e2] at this

  have h1 : (p₁ : ℤ) • β = (r₁ : ℤ) • β' := by
    apply balForms_zsmul_cancel (g := (g : ℤ)) (by exact_mod_cast hg.ne')
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, ← hp₁, ← hr₁, natCast_zsmul, natCast_zsmul]
    exact h

  have hbez : (p₁ : ℤ) * Nat.gcdA p₁ r₁ + (r₁ : ℤ) * Nat.gcdB p₁ r₁ = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  set u := Nat.gcdA p₁ r₁
  set v := Nat.gcdB p₁ r₁
  have hr1 : r₁ = 1 := by
    apply hβ r₁ (u • β' + v • β)
    calc β = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β := by rw [hbez, one_smul]
      _ = u • ((p₁ : ℤ) • β) + (r₁ : ℤ) • (v • β) := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (p₁ : ℤ) u]
      _ = r₁ • (u • β' + v • β) := by
          rw [h1, smul_smul, mul_comm u, ← smul_smul, ← smul_add, natCast_zsmul]
  have hp1 : p₁ = 1 := by
    apply hβ' p₁ (u • β' + v • β)
    calc β' = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β' := by rw [hbez, one_smul]
      _ = (p₁ : ℤ) • (u • β') + v • ((r₁ : ℤ) • β') := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (r₁ : ℤ) v]
      _ = p₁ • (u • β' + v • β) := by
          rw [← h1, smul_smul v, mul_comm v, ← smul_smul, ← smul_add, natCast_zsmul]
  rw [hr1, hp1] at h1
  simpa using h1

end GlobalTheory.PolFan
