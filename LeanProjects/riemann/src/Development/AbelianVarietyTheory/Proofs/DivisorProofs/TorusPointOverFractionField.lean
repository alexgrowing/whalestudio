import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory

theorem exists_compatible_primitive_prime_pow_roots :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharZero k],
      ∃ ζ : ℕ → kˣ, (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) ∧ ∀ r, ζ (r + 1) ^ p = ζ r := by
  intro p hp k _ _ _
  have hp' : p.Prime := hp.out

  have hroot : ∀ u : kˣ, ∃ v : kˣ, v ^ p = u := by
    intro u
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) hp'.pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hp'.ne_zero] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose f hf using hroot

  haveI : NeZero (p : k) := ⟨by exact_mod_cast hp'.ne_zero⟩
  obtain ⟨z₁, hz₁⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k p
  have hz₁0 : z₁ ≠ 0 := hz₁.ne_zero hp'.ne_zero
  have hu₁ : IsPrimitiveRoot (Units.mk0 z₁ hz₁0) p := by
    rw [← IsPrimitiveRoot.coe_units_iff]; simpa using hz₁

  have step : ∀ (n : ℕ) (x : kˣ), IsPrimitiveRoot (x ^ p) (p ^ (n + 1)) →
      IsPrimitiveRoot x (p ^ (n + 2)) := by
    intro n x hx
    rw [IsPrimitiveRoot.iff_orderOf] at hx ⊢
    have hdvd : orderOf x ∣ p ^ (n + 2) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_succ', pow_mul, ← hx, pow_orderOf_eq_one]
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hp').1 hdvd
    rcases Nat.lt_or_ge i (n + 2) with h | h
    · exfalso
      have h1 : (x ^ p) ^ (p ^ n) = 1 := by
        rw [← pow_mul, ← pow_succ', ← orderOf_dvd_iff_pow_eq_one, hio]
        exact Nat.pow_dvd_pow p (by omega)
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hx] at h2
      have := Nat.le_of_dvd (pow_pos hp'.pos n) h2
      have h3 : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp'.one_lt (by omega)
      omega
    · rw [hio, le_antisymm hi h]
  let g : ℕ → kˣ := fun n => Nat.rec (Units.mk0 z₁ hz₁0) (fun _ u => f u) n
  have g0 : g 0 = Units.mk0 z₁ hz₁0 := rfl
  have gs : ∀ n, g (n + 1) = f (g n) := fun n => rfl
  have gprim : ∀ n, IsPrimitiveRoot (g n) (p ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa [g0] using hu₁
    | succ n ih =>
      apply step
      rw [gs, hf]; exact ih
  refine ⟨fun r => match r with | 0 => 1 | r + 1 => g r, ?_, ?_⟩
  · intro r
    cases r with
    | zero => simpa using IsPrimitiveRoot.one
    | succ r => exact gprim r
  · intro r
    cases r with
    | zero => show g 0 ^ p = 1; simpa using (gprim 0).pow_eq_one
    | succ r => show g (r + 1) ^ p = g r; rw [gs, hf]

end GlobalTheory
