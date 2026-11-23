import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.NmHContrPos
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ExteriorWedgeSqZero

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section F1

variable {A : Type*} [CommRing A]

lemma sum_pow_dvd (p : ℕ) (hp : p.Prime) (e : ℕ) {ι' : Type*} (s : Finset ι') (a : ι' → A) :
    (p : A) ∣ (∑ i ∈ s, a i) ^ (p ^ e) - ∑ i ∈ s, a i ^ (p ^ e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, sub_zero]; rw [zero_pow (pow_pos hp.pos e).ne']; exact dvd_zero _
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨t, ht⟩ := exists_add_pow_prime_pow_eq hp (a i) (∑ i ∈ s, a i) e
    obtain ⟨u, hu⟩ := ih
    refine ⟨a i * (∑ i ∈ s, a i) * t + u, ?_⟩
    have : (∑ i ∈ s, a i) ^ (p ^ e) = ∑ i ∈ s, a i ^ (p ^ e) + p * u := by rw [← hu]; ring
    rw [ht, this]; ring

end F1

section Step1

variable {A : Type} [CommRing A] [IsDomain A] {k : ℕ}

theorem step1 (p : ℕ) (hp : p.Prime) (W : A) (hW : W ≠ 0) (hsq : W ^ 2 = (p : A)) (e : ℕ)
    (L L' L2 L2' : Matrix (Finset (Fin k)) (Finset (Fin k)) A) (h1 : L * L' = 1) (h2 : L2' * L2 = 1)
    (hF : ∀ I J, (p : A) ∣ L' I J ^ (p ^ e) - L2' I J)
    (Kv : Finset (Fin k) → A) (o : ℕ) (hd : ∀ J, W ^ o ∣ Matrix.vecMul Kv L J) (J : Finset (Fin k)) :
    W ^ (o * p ^ e) ∣ Matrix.vecMul (powC (p ^ e) Kv) L2 J ∧
    (W ^ (o + 1) ∣ Matrix.vecMul Kv L J → W ^ (o * p ^ e + 1) ∣ Matrix.vecMul (powC (p ^ e) Kv) L2 J ∧
      (0 < e → W ^ (o * p ^ e + 2) ∣ Matrix.vecMul (powC (p ^ e) Kv) L2 J)) := by
  classical
  choose Z hZ using hd
  have hK : Kv = Matrix.vecMul (fun J => W ^ o * Z J) L' := by
    rw [← funext hZ, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]

  have hE : ∀ I, (p : A) ∣ (∑ J, Z J * L' J I) ^ (p ^ e) - ∑ J, Z J ^ (p ^ e) * L2' J I := by
    intro I
    have a1 := sum_pow_dvd p hp e univ (fun J => Z J * L' J I)
    have a2 : (p : A) ∣ ∑ J, (Z J * L' J I) ^ (p ^ e) - ∑ J, Z J ^ (p ^ e) * L2' J I := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun J _ => ?_
      rw [mul_pow, ← mul_sub]; exact Dvd.dvd.mul_left (hF J I) _
    have := dvd_add a1 a2
    simpa using this
  choose ρ hρ using hE
  have hpow : powC (p ^ e) Kv = fun I => W ^ (o * p ^ e) * (Matrix.vecMul (fun J => Z J ^ (p ^ e)) L2' I + p * ρ I) := by
    funext I
    have e1 : Kv I = W ^ o * ∑ J, Z J * L' J I := by
      rw [hK]; simp only [Matrix.vecMul, dotProduct]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring
    have e2 : (∑ J, Z J * L' J I) ^ (p ^ e) = ∑ J, Z J ^ (p ^ e) * L2' J I + p * ρ I := by
      rw [← hρ I]; ring
    simp only [powC]
    rw [e1, mul_pow, ← pow_mul, e2]
    simp only [Matrix.vecMul, dotProduct]
  have hval : Matrix.vecMul (powC (p ^ e) Kv) L2 J =
      W ^ (o * p ^ e) * (Z J ^ (p ^ e) + p * Matrix.vecMul ρ L2 J) := by
    have e3 : powC (p ^ e) Kv = W ^ (o * p ^ e) • (Matrix.vecMul (fun J => Z J ^ (p ^ e)) L2' + (p : A) • ρ) := by
      rw [hpow]; funext I; simp
    rw [e3, Matrix.smul_vecMul, Matrix.add_vecMul, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one, Matrix.smul_vecMul]
    simp
  rw [hval]
  refine ⟨Dvd.intro _ rfl, fun hd1 => ?_⟩
  have hWZ : W ∣ Z J := by
    rw [hZ J, pow_succ] at hd1
    exact (mul_dvd_mul_iff_left (pow_ne_zero o hW)).mp hd1
  obtain ⟨z, hz⟩ := hWZ
  have hQ : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  refine ⟨?_, fun he => ?_⟩
  · rw [pow_succ]
    refine mul_dvd_mul_left _ (dvd_add ?_ ?_)
    · rw [hz]; exact dvd_pow (Dvd.intro _ rfl) (by omega)
    · rw [← hsq, pow_two, mul_assoc]; exact Dvd.intro _ rfl
  · have hQ2 : 2 ≤ p ^ e := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
    rw [pow_add]
    refine mul_dvd_mul_left _ (dvd_add ?_ ?_)
    · rw [hz, mul_pow]; exact Dvd.dvd.mul_right (pow_dvd_pow W hQ2) _
    · rw [← hsq]; exact Dvd.intro _ rfl

end Step1

end Formalism.MainNotions.LemmaBAlt
