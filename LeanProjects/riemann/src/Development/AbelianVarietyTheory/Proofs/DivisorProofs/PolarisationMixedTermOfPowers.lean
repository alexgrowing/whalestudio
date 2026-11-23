import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory

theorem addMonoidHom_intCast_mul_real {A : Type} [CommRing A] (θ : A →+ ℝ) (k : ℤ) (z : A) :
    θ ((k : A) * z) = (k : ℝ) * θ z := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem polarisation_mixed_term_of_powers : ∀ (A : Type) [CommRing A] (θ : A →+ ℝ) (ι : Type) [Fintype ι] (x : Option ι → A) (D : ℕ) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), (∀ n : Option ι → ℤ, Φ (lin (fun o => (n o : ℝ)) ^ (D + 1)) = θ ((∑ o, n o • x o) ^ (D + 1))) → ∀ n : ι → ℤ, Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = θ ((∑ i, n i • x (some i)) ^ D * x none) := by
  intro A _ θ ι _ x D Φ h n
  set Y : MvPolynomial (Option ι) ℝ := MvPolynomial.X none with hY
  set L : MvPolynomial (Option ι) ℝ := rename some (lin fun i => (n i : ℝ)) with hL
  set y : A := ∑ i, n i • x (some i) with hy
  set P : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hP
  set Q : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hQ
  have key : ∀ t : ℤ, P.eval (t : ℝ) = Q.eval (t : ℝ) := by
    intro t
    have ht := h (fun o => Option.elim o t n)
    have hlin : lin (fun o => ((Option.elim o t n : ℤ) : ℝ)) = MvPolynomial.C (t : ℝ) * Y + L := by
      simp only [lin, Fintype.sum_option, Option.elim, hY, hL, map_sum, map_mul, rename_C, rename_X]
    have hsum : (∑ o, (Option.elim o t n) • x o) = (t : A) * x none + y := by
      simp only [Fintype.sum_option, Option.elim, hy, zsmul_eq_mul]
    rw [hlin, hsum, add_pow, add_pow, map_sum, map_sum] at ht
    simp only [hP, hQ, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    have e1 : ∀ a : ℕ, Φ ((MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ))
        = Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : (MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ)
          = ((t : ℝ) ^ a * ((D + 1).choose a : ℝ)) • (Y ^ a * L ^ (D + 1 - a)) := by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, mul_pow, map_natCast]
        ring
      rw [this, map_smul, smul_eq_mul]
      ring
    have e2 : ∀ a : ℕ, θ (((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A))
        = θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : ((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A)
          = (((t ^ a * ((D + 1).choose a : ℤ)) : ℤ) : A) * (x none ^ a * y ^ (D + 1 - a)) := by
        push_cast
        ring
      rw [this, addMonoidHom_intCast_mul_real]
      push_cast
      ring
    simp only [e1, e2] at ht
    exact ht
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun t : ℤ => (t : ℝ)))
    · rintro _ ⟨t, rfl⟩
      exact key t
    · exact Set.infinite_range_of_injective Int.cast_injective
  have hc := congrArg (fun p => Polynomial.coeff p 1) hPQ
  simp only [hP, hQ, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  simp only [Finset.sum_ite_eq, Finset.mem_range] at hc
  rw [if_pos (by omega), if_pos (by omega)] at hc
  · simp only [pow_one, Nat.choose_one_right, Nat.add_sub_cancel] at hc
    have hD : ((D + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at hc hD
    have := mul_right_cancel₀ hD hc
    rw [mul_comm (y ^ D)]
    exact this

end GlobalTheory
