import Formalism.SharpRestriction.GrowthBounds.RootWeights.HeisenbergDividedPowerExpansion

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem descPochhammer_succ_eval_right (j : ℕ) (x : ℤ) :
    (descPochhammer ℤ (j + 1)).eval x = (descPochhammer ℤ j).eval x * (x - j) := by
  rw [descPochhammer_succ_right]
  simp

theorem descPochhammer_succ_eval_add_one (j : ℕ) (x : ℤ) :
    (descPochhammer ℤ (j + 1)).eval (x + 1) = (x + 1) * (descPochhammer ℤ j).eval x := by
  rw [descPochhammer_succ_left]
  simp

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem raise_lower_commutator_on_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} {mu : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSp E mu) : E a b (E b a z) = E b a (E a b z) + (((mu a - mu b : ℤ)) : KK O) • z := by
  have hz' : z ∈ ⨅ c, LinearMap.ker (E c c - ((mu c : ℤ) : KK O) • (1 : Module.End (KK O) V)) := hz
  have hw : ∀ c, E c c z = ((mu c : ℤ) : KK O) • z := by
    intro c
    have h := (Submodule.mem_iInf _).mp hz' c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    exact h
  have hc := congrArg (fun f : Module.End (KK O) V => f z) (hE.1 a b b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, eq_self_iff_true] at hc
  rw [hw a, hw b] at hc
  rw [← sub_eq_iff_eq_add', hc, Int.cast_sub, sub_smul]

theorem raise_lower_pow_commutator_on_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) {mu : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSp E mu) (r : ℕ) :
    E a b (((E b a) ^ r) z) = ((E b a) ^ r) (E a b z) +
      ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • ((E b a) ^ (r - 1)) z := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e1 : ∀ s x, E b a (((E b a) ^ s) x) = ((E b a) ^ (s + 1)) x := by
      intro s x
      rw [pow_succ', Module.End.mul_apply]
    have hy := integral_operator_pow_shifts_weight hE hz b a r
    have h0 := raise_lower_commutator_on_weight (a := a) (b := b) hE hy
    have hA : (mu + (r : ℤ) • rootW b a) a = mu a - r := by
      simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
    have hB : (mu + (r : ℤ) • rootW b a) b = mu b + r := by
      simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
    rw [hA, hB] at h0
    have e2 : ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • E b a (((E b a) ^ (r - 1)) z) =
        ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • ((E b a) ^ r) z := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h
        simp
      · rw [e1, Nat.sub_add_cancel h]
    rw [← e1, h0, ih, map_add, map_smul, e1, e2, Nat.add_sub_cancel, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

theorem raise_pow_lower_pow_expansion {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) {nu : Fin n → ℤ} {y : V}
    (hy : y ∈ weightSp E nu) (k l : ℕ) :
    ((E a b) ^ k) (((E b a) ^ l) y) = ∑ j ∈ range (k + 1),
      ((((k.choose j * l.descFactorial j : ℕ)) : KK O) *
        (((descPochhammer ℤ j).eval (nu a - nu b + k - l) : ℤ) : KK O)) •
        ((E b a) ^ (l - j)) (((E a b) ^ (k - j)) y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have step : ∀ j ∈ range (k + 1),
        E a b (((E b a) ^ (l - j)) (((E a b) ^ (k - j)) y)) =
          ((E b a) ^ (l - j)) (((E a b) ^ (k + 1 - j)) y) +
          (((l - j : ℕ) : KK O) * (((((nu + ((k - j : ℕ) : ℤ) • rootW a b) a -
              (nu + ((k - j : ℕ) : ℤ) • rootW a b) b : ℤ)) : KK O) - ((l - j : ℕ) : KK O) + 1)) •
            ((E b a) ^ (l - (j + 1))) (((E a b) ^ (k + 1 - (j + 1))) y) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hw := integral_operator_pow_shifts_weight hE hy a b (k - j)
      rw [raise_lower_pow_commutator_on_weight hE hab hw (l - j)]
      congr 1
      · rw [← Module.End.mul_apply (E a b), ← pow_succ', show k - j + 1 = k + 1 - j by omega]
      · rw [show l - j - 1 = l - (j + 1) by omega, show k + 1 - (j + 1) = k - j by omega]
    rw [pow_succ', Module.End.mul_apply, ih, map_sum]
    simp only [map_smul]
    refine (Finset.sum_congr rfl (fun j hj => ?_)).trans
      (weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : KK O) *
          (((descPochhammer ℤ j).eval (nu a - nu b + k - l) : ℤ) : KK O))
        (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : KK O) *
          (((descPochhammer ℤ j).eval (nu a - nu b + ((k + 1 : ℕ) : ℤ) - l) : ℤ) : KK O))
        (fun j => ((l - j : ℕ) : KK O) * (((((nu + ((k - j : ℕ) : ℤ) • rootW a b) a -
              (nu + ((k - j : ℕ) : ℤ) • rootW a b) b : ℤ)) : KK O) - ((l - j : ℕ) : KK O) + 1))
        (fun j => ((E b a) ^ (l - j)) (((E a b) ^ (k + 1 - j)) y)) k ?_ ?_ ?_)
    · beta_reduce
      rw [step j hj]
    · simp
    · intro j hj
      beta_reduce
      have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
      have hA : (nu + ((k - j : ℕ) : ℤ) • rootW a b) a = nu a + ((k - j : ℕ) : ℤ) := by
        simp [rootW, Pi.single_apply, hab, hab.symm]
      have hB : (nu + ((k - j : ℕ) : ℤ) • rootW a b) b = nu b - ((k - j : ℕ) : ℤ) := by
        simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
      rw [hA, hB]
      have hx : nu a - nu b + ((k + 1 : ℕ) : ℤ) - (l : ℤ) = (nu a - nu b + (k : ℤ) - (l : ℤ)) + 1 := by
        push_cast
        ring
      rw [hx, descPochhammer_succ_eval_add_one, descPochhammer_succ_eval_right, Nat.choose_succ_succ, Nat.descFactorial_succ]
      have hch : (k.choose (j + 1) : KK O) * ((j : KK O) + 1) = (k.choose j : KK O) * ((k : KK O) - j) := by
        have := congrArg (Nat.cast : ℕ → KK O) (Nat.choose_succ_right_eq k j)
        push_cast [hjk] at this
        exact this
      generalize (descPochhammer ℤ j).eval (nu a - nu b + (k : ℤ) - (l : ℤ)) = P
      by_cases hjl : j ≤ l
      · push_cast [hjk, hjl]
        linear_combination (((l : KK O) - j) * (l.descFactorial j : KK O) * (P : KK O)) * hch
      · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        have h0' : l - j = 0 := by omega
        simp [h0, h0']
    · simp [Nat.choose_succ_self]

theorem raise_lower_dividedPower_binomial [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b)
    {nu : Fin n → ℤ} {y : V} (hy : y ∈ weightSp E nu) (k l : ℕ) :
    divPowE E a b k (divPowE E b a l y) = ∑ j ∈ range (k + 1),
      if j ≤ l then ((Ring.choose (nu a - nu b + k - l) j : ℤ) : KK O) •
        divPowE E b a (l - j) (divPowE E a b (k - j) y) else 0 := by
  simp only [divPowE, LinearMap.smul_apply, map_smul]
  rw [raise_pow_lower_pow_expansion hE hab hy k l, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs with hjl
  · simp only [smul_smul]
    congr 1
    have hP : (descPochhammer ℤ j).eval (nu a - nu b + (k : ℤ) - (l : ℤ)) =
        (j.factorial : ℤ) * Ring.choose (nu a - nu b + (k : ℤ) - (l : ℤ)) j := by
      first
      | rw [Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
      | (rw [Ring.choose]; simp)
    rw [hP]
    have h1 : ((k.factorial : ℕ) : KK O) = (k.choose j : KK O) * j.factorial * (k - j).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
    have h2 : ((l.factorial : ℕ) : KK O) = ((l - j).factorial : KK O) * l.descFactorial j := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjl).symm
    have h3 : (k.choose j : KK O) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
    have h4 : (l.descFactorial j : KK O) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
    have h5 : (j.factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((k - j).factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h7 : ((l - j).factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [h1, h2]
    push_cast
    field_simp
  · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

end hw

end Formalism.MainNotions.G.GLWeightTheory
