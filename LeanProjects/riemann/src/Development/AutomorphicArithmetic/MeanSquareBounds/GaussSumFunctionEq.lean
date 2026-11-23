import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.CharacterBoxes.PairGood
import Development.AutomorphicArithmetic.MeanSquareBounds.Thin
import Development.AutomorphicArithmetic.MeanSquareBounds.realCond
import Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem gauss_sum_function_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HC.An.gChi χ y = G0 χ y := by
  have key : ∀ n ∈ Icc 1 ⌊y⌋₊, max (y / (n : ℝ) - 1) 0 = y / n - 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hy1 : 1 ≤ y := Nat.floor_pos.1 (by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))
    have : 1 ≤ y / n := by rw [le_div_iff₀ (by linarith)]; linarith
    exact max_eq_left (by linarith)
  unfold Formalism.HC.An.gChi G0
  by_cases h : χ = 1
  · simp only [h, if_true]
    congr 1
    unfold Formalism.HC.An.G G1
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [key n hn]
  · simp only [h, if_false]
    unfold Formalism.HC.An.sumLamChi Gchi
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [key n hn]

private theorem isReal_of_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h2 : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  by_cases ha : IsUnit a
  · have h := congrArg (fun f : DirichletCharacter ℂ N => f a) h2
    simp only [pow_two, MulChar.one_apply ha] at h
    rw [MulChar.mul_apply] at h
    have hz : χ a = 1 ∨ χ a = -1 := by
      have : (χ a - 1) * (χ a + 1) = 0 := by ring_nf; rw [← pow_two] at h; rw [h]; ring
      rcases mul_eq_zero.1 this with h1 | h1
      · left; linear_combination h1
      · right; linear_combination h1
    rcases hz with hz | hz <;> simp [hz]
  · simp [MulChar.map_nonunit χ ha]

private theorem level_dvd {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : H.IsCharE χ) : N ∣ H.condN := by
  obtain ⟨θ, hθ⟩ := h
  have hp : (Formalism.HC.PChar.mk N χ hθ.1) = H.prim θ := (H.isPrimOf_iff θ (Formalism.HC.PChar.mk N χ hθ.1)).1 hθ
  have hN : N = (H.prim θ).N := congrArg Formalism.HC.PChar.N hp
  rw [hN]
  exact DirichletCharacter.conductor_dvd_level (H.dir θ)

theorem thinH :
    UpperTheory.Top.ThinH := by
  refine ⟨1, one_pos, fun B eps he he52 => ?_⟩
  obtain ⟨c₀s, hc₀s, hsmall⟩ := small_zeros (8 * ⌊B⌋₊)
  have hc₀ : 0 < min c₀s (1 / 400) := lt_min hc₀s (by norm_num)
  obtain ⟨x₀, hx₀⟩ := thin eps 2 1 (min c₀s (1 / 400)) he two_pos one_pos hc₀
  refine ⟨x₀, fun x hx φ H hB hlog hRB => ?_⟩
  intro N _ χ hχ y hy
  rw [gauss_sum_function_eq]
  have hprim : χ.IsPrimitive := by
    obtain ⟨θ, hθ⟩ := hχ
    exact hθ.1
  have hNd : N ∣ H.condN := level_dvd H χ hχ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hlogN : Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 :=
    (Real.log_le_log (by exact_mod_cast hNpos)
      (by exact_mod_cast Nat.le_of_dvd H.condN_pos hNd)).trans hlog
  refine hx₀ x hx N χ hprim hlogN ?_ y hy
  intro h2 h1 β hβ hβ1
  have hq : H.q.Prime := H.hyp.1
  have hd : H.d.Prime := H.hyp.2.1
  by_cases hqd : H.q ∣ N ∨ H.d ∣ N
  · exact hRB (Formalism.HC.PChar.mk N χ hprim) hχ (isReal_of_sq χ h2) hqd β
      (by have := min_le_right c₀s (1 / 400); linarith)
  · push_neg at hqd
    have hQ0 : H.QS ≠ 0 := (H.QS_pos).ne'
    have hsplitQ := Nat.ordProj_mul_ordCompl_eq_self H.QS 2
    have hprimes : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ 8 * (H.QS / 2 ^ H.QS.factorization 2) ∨ p = H.q ∨ p = H.d := by
      intro p hp hpN
      have hpc : p ∣ H.QS * H.q * H.d := hpN.trans hNd
      rcases (Nat.Prime.dvd_mul hp).1 hpc with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
        · left
          by_cases hp2 : p = 2
          · subst hp2
            exact Dvd.dvd.mul_right (by norm_num) _
          · apply Dvd.dvd.mul_left
            rw [← hsplitQ] at h'
            have hcop : Nat.Coprime p (2 ^ H.QS.factorization 2) :=
              Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
            exact hcop.dvd_of_dvd_mul_left h'
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h'))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hd).1 h))
    have hdiv := real_cond (8 * (H.QS / 2 ^ H.QS.factorization 2)) H.q H.d N χ hprim h2
      (dvd_mul_right 8 _) hq hd hprimes
    have hcq : Nat.Coprime N H.q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd.1).symm
    have hcd : Nat.Coprime N H.d := ((Nat.Prime.coprime_iff_not_dvd hd).2 hqd.2).symm
    have hN0 : N ∣ 8 * (H.QS / 2 ^ H.QS.factorization 2) :=
      hcq.dvd_of_dvd_mul_right (hcd.dvd_of_dvd_mul_right hdiv)
    have hopos : 0 < H.QS / 2 ^ H.QS.factorization 2 := Nat.ordCompl_pos 2 hQ0
    have hofl : H.QS / 2 ^ H.QS.factorization 2 ≤ ⌊B⌋₊ := Nat.le_floor hB
    have hNle : N ≤ 8 * ⌊B⌋₊ := (Nat.le_of_dvd (by omega) hN0).trans (by omega)
    exact hsmall N χ hNle h1 β (by have := min_le_left c₀s (1 / 400); linarith) hβ1

end QH
