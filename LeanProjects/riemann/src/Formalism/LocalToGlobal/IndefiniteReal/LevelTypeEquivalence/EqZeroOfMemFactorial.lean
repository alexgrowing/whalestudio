import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA

namespace Formalism.IndefR.Eqv.AdelDual

open Filter Topology

section Val

open IsDedekindDomain NumberField

theorem exists_pow_lt {c a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hc : c < 1) : ∃ k : ℕ, c ^ k < a := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨1, by simpa using (zero_lt_iff.mpr ha)⟩
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.mp hc0
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  have hα : Multiplicative.toAdd α < 0 := by
    have h1 : ((α : WithZero (Multiplicative ℤ))) < ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using hc
    rw [WithZero.coe_lt_coe] at h1
    exact h1
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (α ^ ((Multiplicative.toAdd β).natAbs + 1)) < Multiplicative.toAdd β
  rw [toAdd_pow, nsmul_eq_mul]
  set a := Multiplicative.toAdd α
  set b := Multiplicative.toAdd β
  have ha1 : a ≤ -1 := by omega
  have h2 : -((b.natAbs : ℕ) : ℤ) ≤ b := by omega
  have h3 : (((b.natAbs + 1 : ℕ) : ℤ)) * a ≤ -(((b.natAbs + 1 : ℕ) : ℤ)) := by
    have : (0 : ℤ) ≤ ((b.natAbs + 1 : ℕ) : ℤ) := by positivity
    nlinarith
  push_cast at h3 ⊢
  have h4 := neg_abs_le b
  linarith

variable {F : Type} [Field F] [NumberField F]

theorem val_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Valued.v (n : v.adicCompletion F) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ]; exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

theorem val_factorial_anti (v : HeightOneSpectrum (𝓞 F)) {m m' : ℕ} (h : m ≤ m') :
    Valued.v ((m'.factorial : ℕ) : v.adicCompletion F) ≤ Valued.v ((m.factorial : ℕ) : v.adicCompletion F) := by
  induction m', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, map_mul]
    calc Valued.v ((k + 1 : ℕ) : v.adicCompletion F) * Valued.v ((k.factorial : ℕ) : v.adicCompletion F)
        ≤ 1 * Valued.v ((k.factorial : ℕ) : v.adicCompletion F) :=
          mul_le_mul' (val_natCast_le_one v (k + 1)) le_rfl
      _ = _ := one_mul _
      _ ≤ _ := ih

theorem val_factorial_le (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    Valued.v (((N * k).factorial : ℕ) : v.adicCompletion F) ≤ Valued.v ((N : ℕ) : v.adicCompletion F) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, N * (k + 1) = m + 1 := ⟨N * (k + 1) - 1, by
      have : 1 ≤ N * (k + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega⟩
    rw [hm, Nat.factorial_succ, Nat.cast_mul, map_mul, pow_succ, mul_comm (Valued.v _ ^ k)]
    have h1 : Valued.v ((m + 1 : ℕ) : v.adicCompletion F) ≤ Valued.v ((N : ℕ) : v.adicCompletion F) := by
      rw [← hm, Nat.cast_mul, map_mul]
      calc Valued.v ((N : ℕ) : v.adicCompletion F) * Valued.v ((k + 1 : ℕ) : v.adicCompletion F)
          ≤ Valued.v ((N : ℕ) : v.adicCompletion F) * 1 := mul_le_mul' le_rfl (val_natCast_le_one v _)
        _ = _ := mul_one _
    have h2 : Valued.v ((m.factorial : ℕ) : v.adicCompletion F) ≤ Valued.v ((N : ℕ) : v.adicCompletion F) ^ k :=
      (val_factorial_anti v (by
        have : N * k + N = m + 1 := by rw [← hm]; ring
        omega)).trans ih
    exact mul_le_mul' h1 h2

theorem exists_nat_val_lt_one (v : HeightOneSpectrum (𝓞 F)) :
    ∃ N : ℕ, 1 ≤ N ∧ Valued.v ((N : ℕ) : v.adicCompletion F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · have e : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) = (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) :
        v.adicCompletion F) := by
      exact (map_natCast (algebraMap (𝓞 F) (v.adicCompletion F)) _).symm
    rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.absNorm_mem _

theorem eq_zero_of_mem_factorial (x : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ n : ℕ, ∃ y ∈ Formalism.IndefR.PHeisFC.Ohat F, x = n.factorial • y) : x = 0 := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  by_contra hne
  have hne' : x v ≠ 0 := fun h0 => hne (by exact h0)
  have hx0 : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne'
  obtain ⟨N, hN1, hN⟩ := exists_nat_val_lt_one v
  obtain ⟨k, hk⟩ := exists_pow_lt hx0 hN
  obtain ⟨y, hy, rfl⟩ := h (N * k)
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hy v)
  have e : ((N * k).factorial • y) v = (((N * k).factorial : ℕ) : v.adicCompletion F) * y v := by
    rw [nsmul_eq_mul]; rfl
  have : Valued.v (((N * k).factorial • y) v) ≤ Valued.v ((N : ℕ) : v.adicCompletion F) ^ k := by
    rw [e, map_mul]
    calc _ ≤ Valued.v (((N * k).factorial : ℕ) : v.adicCompletion F) * 1 := mul_le_mul' le_rfl hyv
      _ = _ := mul_one _
      _ ≤ _ := val_factorial_le v N hN1 k
  exact absurd (lt_of_le_of_lt this hk) (lt_irrefl _)

end Val

end Formalism.IndefR.Eqv.AdelDual
