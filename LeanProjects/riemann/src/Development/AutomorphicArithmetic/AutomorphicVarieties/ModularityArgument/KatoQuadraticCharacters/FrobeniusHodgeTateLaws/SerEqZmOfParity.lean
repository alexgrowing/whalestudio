import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerVal

noncomputable section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.EisM GlobalTheory.KummerEisensteinGalois

namespace UpperTheory.V.Z.Kato.Joint

def twb (N : ℕ) (s : ℂ) (b : ℤ) : ℤ → ℂ := fun B =>
  (if (B : ZMod N) = b then 1 else 0) - s * (if (B : ZMod N) = -b then 1 else 0)

theorem Uo_iterate {R : Type*} [CommRing R] (l m : ℕ) (f : ℕ → R) (i : ℕ) : (Uo l)^[m] f i = f (l ^ m * i) := by
  induction m generalizing f with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, ih, Uo, pow_succ', mul_assoc]

private def hz {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (z : ZMod N) : ℂ :=
  ∑ y : ZMod N, θ y * ZMod.stdAddChar (y * z)

private theorem hat_hz {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (d : ℤ) : hat θ d = hz θ (d : ZMod N) := by
  unfold hat hz
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) (fun _ _ => Finset.mem_univ _)
    (fun y _ => Finset.mem_range.mpr (ZMod.val_lt y)) (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.mp hi))
    (fun y _ => ZMod.natCast_zmod_val y) (fun i _ => ?_)
  have h : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
  rw [h, ZMod.stdAddChar_coe]
  push_cast
  rfl

private theorem hz_unit {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (z : ZMod N) (u : (ZMod N)ˣ) :
    hz θ (z * (u⁻¹ : (ZMod N)ˣ)) = θ u * hz θ z := by
  unfold hz
  rw [Finset.mul_sum, ← Equiv.sum_comp (Units.mulLeft u)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h : (u : ZMod N) * y * (z * (u⁻¹ : (ZMod N)ˣ)) = y * z := by
    calc _ = ((u : ZMod N) * (u⁻¹ : (ZMod N)ˣ)) * (y * z) := by ring
      _ = _ := by simp
  simp only [Units.mulLeft_apply, h, map_mul, mul_assoc]

private theorem hz_neg {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (z : ZMod N) :
    hz θ (-z) = θ (-1) * hz θ z := by
  simpa using hz_unit θ z (-1)

private theorem wsum {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (A : ZMod N) (s c : ℂ) :
    ∑ x : ZMod N, hz θ x / 2 * ((if A = x * u then c else 0) + (if -A = x * u then s * c else 0)) =
      θ u * ((1 + s * θ (-1)) / 2) * (hz θ A * c) := by
  have h : ∀ (A x : ZMod N), A = x * u ↔ A * (u⁻¹ : (ZMod N)ˣ) = x := fun A x => (Units.mul_inv_eq_iff_eq_mul u).symm
  simp only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hz_unit, hz_unit, hz_neg]
  ring

private theorem ff_eq {l : ℕ} [hl : Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a : ℤ) (hk : 3 ≤ k) (ho : Odd k) (s : ℕ) :
    ι (ffMu N l m k ψ a s) = ∑ p ∈ s.divisorsAntidiagonal, if l ∣ s then 0 else
      ((if (p.1 : ZMod N) = a then ι (ψ p.1) * (p.1 : ℂ) ^ (k - 2) else 0) +
        (if -(p.1 : ZMod N) = a then ι (ψ (-1)) * (ι (ψ p.1) * (p.1 : ℂ) ^ (k - 2)) else 0)) := by
  have ho' : Odd (k - 2) := Nat.Odd.sub_even (by omega) ho (by decide)
  rw [Nat.sum_divisorsAntidiagonal' (fun A _ => if l ∣ s then 0 else
      ((if (A : ZMod N) = a then ι (ψ A) * (A : ℂ) ^ (k - 2) else 0) +
        (if -(A : ZMod N) = a then ι (ψ (-1)) * (ι (ψ A) * (A : ℂ) ^ (k - 2)) else 0))), ffMu, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hs : l ∣ s ↔ ¬ (¬ l ∣ d ∧ ¬ l ∣ s / d) := by
    conv_lhs => rw [← Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    rw [hl.out.dvd_mul]; tauto
  generalize s / d = A at hs ⊢
  simp only [← ZMod.intCast_eq_intCast_iff, hs, ite_not, Int.cast_neg, Int.cast_natCast]
  rw [← neg_one_mul (A : ZMod (l ^ m)), map_mul, ho'.neg_pow]
  split_ifs <;> simp [mul_assoc]

private theorem ee_eq {l : ℕ} [hl : Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N m : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (b : ℤ) (s : ℕ) :
    ι (eeMu N l m ψ b s) = ∑ p ∈ s.divisorsAntidiagonal, if l ∣ s then 0 else
      twb N (ι (ψ (-1))) b p.1 * ι (ψ ((p.2 : ZMod (l ^ m))⁻¹)) := by
  rw [Nat.sum_divisorsAntidiagonal' (fun B d => if l ∣ s then 0 else
      twb N (ι (ψ (-1))) b B * ι (ψ ((d : ZMod (l ^ m))⁻¹))), eeMu, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hs : l ∣ s ↔ ¬ (¬ l ∣ d ∧ ¬ l ∣ s / d) := by
    conv_lhs => rw [← Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    rw [hl.out.dvd_mul]; tauto
  generalize s / d = B at hs ⊢
  simp only [← ZMod.intCast_eq_intCast_iff, hs, ite_not, Int.cast_neg, Int.cast_natCast, twb, neg_eq_iff_eq_neg]
  by_cases h : ¬ l ∣ d ∧ ¬ l ∣ B
  · rw [if_pos h, if_pos h]
    have hu : IsUnit (d : ZMod (l ^ m)) :=
      (ZMod.isUnit_iff_coprime d (l ^ m)).mpr (Nat.Coprime.pow_right m ((hl.out.coprime_iff_not_dvd.mpr h.1).symm))
    have h1 : ψ⁻¹ (d : ZMod (l ^ m)) = ψ ((d : ZMod (l ^ m))⁻¹) := by
      rw [MulChar.inv_apply_eq_inv']
      refine (eq_inv_of_mul_eq_one_right ?_).symm
      rw [← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
    have h2 : ψ⁻¹ (-1) = ψ (-1) := by
      rw [MulChar.inv_apply_eq_inv']
      refine (eq_inv_of_mul_eq_one_right ?_).symm
      rw [← map_mul]; simp
    rw [← neg_one_mul (d : ZMod (l ^ m)), map_mul, h1, h2]
    split_ifs <;> simp [sub_mul]
  · rw [if_neg h, if_neg h, map_zero]

theorem ser_eq_Zm {l : ℕ} [hl : Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ) (hk : 3 ≤ k) (ho : Odd k) (ha : IsCoprime a N) (i : ℕ) :
    ι (ser ι N θ m k ψ a b i) = θ (a : ZMod N) * ((1 + ι (ψ (-1)) * θ (-1)) / 2) *
      (Uo l)^[m] (Zm k l (hat θ) (twb N (ι (ψ (-1))) b)
        fun A d => ι (ψ ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) i := by
  obtain ⟨u, hu⟩ : IsUnit (a : ZMod N) := (ZMod.coe_int_isUnit_iff_isCoprime a N).mpr ha.symm
  have hff : ∀ s : ℕ, ∑ x : ZMod N, hat θ (x.val : ℤ) / 2 * ι (ffMu N l m k ψ ((x.val : ℤ) * a) s) =
      θ (a : ZMod N) * ((1 + ι (ψ (-1)) * θ (-1)) / 2) * ∑ p ∈ s.divisorsAntidiagonal, if l ∣ s then 0 else
        hat θ p.1 * (ι (ψ p.1) * (p.1 : ℂ) ^ (k - 2)) := by
    intro s
    simp only [ff_eq ι N m k ψ _ hk ho, Finset.mul_sum, hat_hz]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : l ∣ s
    · simp [h]
    · simp only [h, if_false, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, ← hu]
      exact wsum θ u _ _ _
  rw [Uo_iterate, ser, up]
  generalize l ^ m * i = n
  simp only [coPtMu, ← mul_eq_cmul, mul, map_sum, map_mul, RingEquiv.apply_symm_apply, Finset.mul_sum, Zm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, hff, ee_eq, mul_assoc, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases h1 : l ∣ p.1 <;> by_cases h2 : l ∣ p.2 <;> simp [h1, h2]
  left; ring

theorem ser_eq_Zm_of_parity {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N)
    (m k : ℕ) (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ) (hk : 3 ≤ k) (ho : Odd k) (ha : IsCoprime a N)
    (hs : ι (ψ (-1)) = θ (-1)) (i : ℕ) :
    ι (ser ι N θ m k ψ a b i) = θ (a : ZMod N) *
      (Uo l)^[m] (Zm k l (hat θ) (twb N (θ (-1)) b)
        fun A d => ι (ψ ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) i := by
  rw [ser_eq_Zm ι N θ m k ψ a b hk ho ha, hs, ← map_mul]
  simp

end UpperTheory.V.Z.Kato.Joint

end
