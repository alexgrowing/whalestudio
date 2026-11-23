import Mathlib
import Formalism.GL3MeanSquares.SignsFromTrianglesSquares

open Finset

namespace Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower

open Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.IntegralLatticeDensity

theorem t_swap : ModelCocycleTwoSwapped := by
  intro δ a b h; field_simp; ring

theorem t_heis : HeisenbergCocycle := by
  intro V _ H hadd hherm F x y z
  have hadd2 : ∀ x y y', H x (y + y') = H x y + H x y' := by
    intro x y y'; rw [hherm (y+y') x, hadd, map_add, ← hherm, ← hherm]
  have hc : H y x = H x y - 2 * Complex.I * ((H x y).im : ℂ) := by
    rw [hherm x y]; apply Complex.ext <;> simp <;> ring
  unfold Heisenberg₂
  rw [add_assoc, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [hadd, hadd2]
  rw [hc]
  ring

theorem t_odd : OddOrderDetermined := by
  intro G H _ _ _ Φ Φ' B hodd h h' he he' x
  let c : Multiplicative G →* H :=
    { toFun := fun g => Φ (Multiplicative.toAdd g) * (Φ' (Multiplicative.toAdd g))⁻¹
      map_one' := by
        have a := h 0 0; have a' := h' 0 0
        simp only [add_zero] at a a'
        have : Φ 0 * B 0 0 = 1 := by
          have := a; rw [mul_assoc] at this; exact (mul_eq_left.mp this.symm)
        have t' : Φ' 0 * B 0 0 = 1 := by
          have := a'; rw [mul_assoc] at this; exact (mul_eq_left.mp this.symm)
        show Φ 0 * (Φ' 0)⁻¹ = 1
        rw [mul_inv_eq_one]; exact mul_right_cancel (this.trans t'.symm)
      map_mul' := by
        intro g g'
        show Φ (_ + _) * (Φ' (_ + _))⁻¹ = _
        rw [h, h']; simp only [mul_inv];
        rw [show ∀ a b c d e f : H, a * b * c * (d * e * f) = (a * d) * (b * e) * (c * f) from by
          intros; ac_rfl]
        simp }
  have hc2 : ∀ g, c g ^ 2 = 1 := by
    intro g
    have : c g⁻¹ = c g := by
      show Φ (-_) * (Φ' (-_))⁻¹ = Φ _ * (Φ' _)⁻¹
      rw [he, he']
    rw [pow_two]; nth_rewrite 2 [← this]; rw [← map_mul]; simp
  have hcn : ∀ g, c g ^ Fintype.card G = 1 := by
    intro g; rw [← map_pow]
    have : g ^ Fintype.card (Multiplicative G) = 1 := pow_card_eq_one
    have e : Fintype.card (Multiplicative G) = Fintype.card G := by simp
    rw [← e, this, map_one]
  obtain ⟨k, hk⟩ := hodd
  have : c (Multiplicative.ofAdd x) = 1 := by
    have a := hcn (Multiplicative.ofAdd x)
    rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at a; exact a
  exact mul_inv_eq_one.mp this

example : ∀ a b : ZMod 2, a.val % 2 = b.val % 2 →
    (∑ _r : Unit, (1 : ZMod 5) * 1) = if a = b then 1 else 0 := by decide

example (p : ℕ) (hp : p.Prime) : ∀ a ∈ (algebraMap ℤ ℚ).range, ∃ b ∈ (algebraMap ℤ ℚ).range,
    (RingHom.id ℚ) a - a ^ p = (p : ℚ) * b := by
  rintro _ ⟨n, rfl⟩
  haveI := Fact.mk hp
  have : (p : ℤ) ∣ n - n ^ p := by
    rw [← (ZMod.intCast_zmod_eq_zero_iff_dvd _ p)]; push_cast; rw [ZMod.pow_card]; ring
  obtain ⟨k, hk⟩ := this
  refine ⟨k, ⟨k, rfl⟩, ?_⟩
  have := congrArg (fun z : ℤ => (z : ℚ)) hk
  simpa using this

section
variable {V : Type} [AddCommGroup V] {H : V → V → ℂ}

theorem add2 (hadd : ∀ x x' y, H (x + x') y = H x y + H x' y)
    (hherm : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) : ∀ x y y', H x (y + y') = H x y + H x y' := by
  intro x y y'; rw [hherm (y+y') x, hadd, map_add, ← hherm, ← hherm]

theorem sub2 (hadd : ∀ x x' y, H (x + x') y = H x y + H x' y)
    (hherm : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) : ∀ x y y', H x (y - y') = H x y - H x y' := by
  intro x y y'; have := add2 hadd hherm x (y - y') y'; rw [sub_add_cancel] at this; rw [this]; ring
end

example : ∀ a : Fin 3 → ZMod 3, (∑ j, a j) ^ 2 =
    (∑ j, (a j) ^ 2) + ∑ j, ∑ j' ∈ univ.filter (fun j' => j < j'), cob (fun x : ZMod 3 => x ^ 2) (a j) (a j') := by
  decide +kernel

theorem rv_sumexp : SumExpansion := by
  intro M Q _ _ φ hadd k
  have h00 : ∀ b, cob φ 0 b = 0 := by
    intro b; have := hadd 0 0 b; simpa using this
  have hφ0 : φ 0 = 0 := by
    have := h00 0; simpa [cob] using this
  have hsum : ∀ (n : ℕ) (c : Fin n → M) (b : M), cob φ (∑ j, c j) b = ∑ j, cob φ (c j) b := by
    intro n
    induction n with
    | zero => intro c b; simp [h00]
    | succ n ih => intro c b; rw [Fin.sum_univ_castSucc, hadd, ih, Fin.sum_univ_castSucc]
  induction k with
  | zero => intro a; simp [hφ0]
  | succ k ih =>
    intro a
    have e1 : φ (∑ j, a j) = φ (∑ j : Fin k, a j.castSucc) + φ (a (Fin.last k)) +
        ∑ j : Fin k, cob φ (a j.castSucc) (a (Fin.last k)) := by
      rw [Fin.sum_univ_castSucc, ← hsum]; simp [cob]
    rw [e1, ih (fun j => a j.castSucc)]
    simp only [Finset.sum_filter]
    rw [Fin.sum_univ_castSucc (f := fun j => φ (a j)),
      Fin.sum_univ_castSucc (f := fun j => ∑ j', if j < j' then cob φ (a j) (a j') else 0)]
    simp only [Fin.sum_univ_castSucc (n := k), Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last,
      if_true, Finset.sum_add_distrib]
    have : ∀ j : Fin k, ¬ (Fin.last k < j.castSucc) := fun j => by
      simp [Fin.le_last]
    simp [this]
    abel

theorem rv_gram : GramExpansion := by
  intro Z O M Q _ _ _ _ _ _ _ φ nm hadd hadj hnm n _ k A u
  classical
  have hs := rv_sumexp M Q φ hadd k
  have h00 : ∀ b, cob φ 0 b = 0 := by
    intro b; have := hadd 0 0 b; simpa using this
  have hsumF : ∀ (s : Finset n) (c : n → M) (b : M),
      cob φ (∑ i ∈ s, c i) b = ∑ i ∈ s, cob φ (c i) b := by
    intro s c b
    induction s using Finset.induction_on with
    | empty => simp [h00]
    | insert a s ha ih => rw [sum_insert ha, sum_insert ha, hadd, ih]
  simp_rw [hs, hnm]
  rw [sum_add_distrib]
  congr 1
  · rw [sum_comm]; simp [sum_smul]
  · rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j' _ => ?_
    rw [sum_smul, hsumF]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_smul, hadj (star (A i j')) (A i j • u j) (u j'), star_star]

end Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower

namespace Formalism.HermitianLattices.WeilRepresentation

theorem model_cocycle_two_swapped : ModelCocycleTwoSwapped := CocycleEighthPower.t_swap
theorem heisenberg_cocycle : HeisenbergCocycle := CocycleEighthPower.t_heis
theorem gram_expansion : GramExpansion := CocycleEighthPower.rv_gram

end Formalism.HermitianLattices.WeilRepresentation
