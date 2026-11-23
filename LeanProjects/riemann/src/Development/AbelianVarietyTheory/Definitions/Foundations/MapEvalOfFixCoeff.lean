import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem HTPres.eval_ne_zero {A : ValuationSubring Ω} {c : Coef l} {m : ℕ} {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {ζ : Ω}
    {ι : Type} [Fintype ι] {P : ι → Polynomial Ω} {o : ι → Qbar l} (h : HTPres A c m Z ζ P o) (i : ι) : (P i).eval ζ ≠ 0 :=
  (h.2.2.2.2.2.1 i).2.1

theorem HTPres.ne_zero {A : ValuationSubring Ω} {c : Coef l} {m : ℕ} {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {ζ : Ω}
    {ι : Type} [Fintype ι] {P : ι → Polynomial Ω} {o : ι → Qbar l} (h : HTPres A c m Z ζ P o) (i : ι) : P i ≠ 0 := by
  intro h0
  exact h.eval_ne_zero i (by rw [h0, Polynomial.eval_zero])

theorem HTLawAt.mono {A : ValuationSubring Ω} {c : Coef l} {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {j : Ω →+* Qbar l}
    {m₀ m₁ c₀ : ℕ} {Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l} (h : HTLawAt A c Z j m₀ c₀ Rhs)
    (hm : m₀ ≤ m₁) : HTLawAt A c Z j m₁ c₀ Rhs :=
  fun m hm' => h m (hm.trans hm')

theorem tval_coe (Q : Polynomial (Qbar l)) {N : ℕ} (hN : Q.natDegree < N) (z : Qbar l) :
    tval (Q : PowerSeries (Qbar l)) N z = Q.eval (z - 1) := by
  rw [Polynomial.eval_eq_sum_range' hN]
  simp only [tval, Polynomial.coeff_coe]

theorem tval_dirac {y N : ℕ} (hN : y < N) (z : Qbar l) : tval ((1 + PowerSeries.X) ^ y) N z = z ^ y := by
  have h : (((1 + Polynomial.X) ^ y : Polynomial (Qbar l)) : PowerSeries (Qbar l)) = (1 + PowerSeries.X) ^ y := by simp
  rw [← h, tval_coe _ (lt_of_le_of_lt _ hN)]
  · simp
  · refine Polynomial.natDegree_pow_le.trans ?_
    rw [add_comm, ← Polynomial.C_1, Polynomial.natDegree_X_add_C, mul_one]

theorem mass_dirac {r : ℕ} {ξ : Qbar l} (hξ : IsPrimitiveRoot ξ (l ^ r)) {x y : ℕ} (hx : x < l ^ r) (hy : y < l ^ r) :
    mass ((1 + PowerSeries.X) ^ y) r ξ x = if x = y then ((l : ℕ) : Qbar l) ^ r else 0 := by
  have h0 : ξ ≠ 0 := hξ.ne_zero (by omega)
  have hy' : y < l ^ (3 * r) := hy.trans_le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (by omega))
  have e : ∀ k, ξ ^ (l ^ r - (k * x) % l ^ r) * tval ((1 + PowerSeries.X) ^ y) (l ^ (3 * r)) (ξ ^ k) = (ξ ^ y / ξ ^ x) ^ k := by
    intro k
    rw [tval_dirac hy', pow_sub₀ _ h0 (Nat.mod_lt _ (by omega)).le, hξ.pow_eq_one,
      ← pow_eq_pow_mod _ hξ.pow_eq_one, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm x k, mul_comm y k]
    field_simp
  simp only [mass, e]
  split_ifs with h1
  · subst h1; simp [h0]
  · have hne : ξ ^ y / ξ ^ x ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq (pow_ne_zero _ h0)] at h
      exact h1 (hξ.pow_inj hx hy h.symm)
    have := mul_geom_sum (ξ ^ y / ξ ^ x) (l ^ r)
    rw [div_pow, ← pow_mul, ← pow_mul, mul_comm x, mul_comm y, pow_mul, pow_mul, hξ.pow_eq_one, one_pow, one_pow, div_one,
      sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

example (j : Ω →+* Qbar l) (ζ : Ω) (hζ : ζ ≠ 0) (b : ℕ) :
    htv j ζ (fun _ : Unit => Polynomial.X) (fun _ => 1) b = 1 := by
  simp [htv, hζ]

example (j : Ω →+* Qbar l) (ζ : Ω) (b : ℕ) :
    htv j ζ (fun _ : Unit => 1 + Polynomial.X) (fun _ => 1) b = j (ζ ^ b / (1 + ζ ^ b)) := by
  simp [htv]

end GlobalTheory.KZ
