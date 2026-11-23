import Formalism.CharacterColumnKernels.Statement

open Finset

namespace Formalism.NG

private lemma vInt_eq_emult (l : ℕ) [hl : Fact l.Prime] {z : ℤ} (hz : z ≠ 0) :
    (padicValInt l z : ℕ∞) = emultiplicity (l : ℤ) z := by
  rw [padicValInt.of_ne_one_ne_zero hl.out.ne_one hz]
  exact (FiniteMultiplicity.emultiplicity_eq_multiplicity
    (Int.finiteMultiplicity_iff.mpr ⟨by simpa using hl.out.ne_one, hz⟩)).symm

theorem powSubPow : StatPowSubPow := by
  intro l hl hl2 x hx1 hx2 a b hab
  have hp : l.Prime := hl.out
  have hodd : Odd l := hp.odd_of_ne_two hl2
  have hpi : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by
      have := dvd_sub h hx1
      simpa using this
    exact hpi.not_dvd_one h1
  have hx1ne : x - 1 ≠ 0 := by
    intro h; exact hx2 (by rw [h]; exact dvd_zero _)
  have hv1 : padicValInt l (x - 1) = 1 := by
    have h1 := (padicValInt_dvd_iff (p := l) 1 (x - 1)).mp (by simpa using hx1)
    have h2 : ¬ (2 ≤ padicValInt l (x - 1)) := fun h =>
      hx2 ((padicValInt_dvd_iff (p := l) 2 (x - 1)).mpr (Or.inr h))
    rcases h1 with h1 | h1
    · exact absurd h1 hx1ne
    · omega
  set n := b - a with hn
  have hn0 : n ≠ 0 := by omega
  have hlte := Int.emultiplicity_pow_sub_pow hp hodd (x := x) (y := 1) (by simpa using hx1) hx n
  rw [one_pow] at hlte
  rw [← vInt_eq_emult l hx1ne, hv1, ← padicValNat_eq_emultiplicity_of_ne_one hp.ne_one hn0] at hlte
  have hne : x ^ n - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hlte
    have h' : ((1 + padicValNat l n : ℕ) : ℕ∞) = ⊤ := by push_cast; exact hlte.symm
    exact ENat.natCast_ne_top _ h'
  have hv : padicValInt l (x ^ n - 1) = 1 + padicValNat l n := by
    rw [← vInt_eq_emult l hne] at hlte
    exact_mod_cast hlte
  have hxa : x ^ a ≠ 0 := pow_ne_zero _ (fun h => hx (by rw [h]; exact dvd_zero _))
  have hfac : x ^ b - x ^ a = x ^ a * (x ^ n - 1) := by
    have : b = a + n := by omega
    rw [this, pow_add]; ring
  rw [hfac, padicValInt.mul hxa hne, hv,
    padicValInt.eq_zero_of_not_dvd (fun h => hx (hpi.dvd_of_dvd_pow h))]
  ring

private lemma prod_erase_zero {M : Type*} [CommMonoid M] (t : ℕ) (f : Fin (t + 1) → M) :
    ∏ i ∈ univ.erase (0 : Fin (t + 1)), f i = ∏ i : Fin t, f i.succ := by
  rw [Fin.univ_succ, Finset.erase_cons, Finset.prod_map]
  rfl

theorem deltaVal : StatDeltaVal := by
  intro l hl hl2 u hu w t
  have hp : l.Prime := hl.out
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hp.two_le
  have hnot : ¬ (l : ℤ) ^ 2 ∣ (1 + (l : ℤ)) - 1 := by
    rw [show (1 + (l : ℤ)) - 1 = (l : ℤ) by ring]
    intro h
    have := Int.le_of_dvd (by omega) h
    nlinarith
  have hF : ∀ i : ℕ, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) ≠ 0 ∧
      padicValInt l (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) =
        1 + padicValNat l (i + 1) := by
    intro i
    have hrw : u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)) =
        (-u) * ((1 + (l : ℤ)) ^ (w + (i + 1)) - (1 + (l : ℤ)) ^ w) := by ring
    have hps := powSubPow l hl2 (1 + (l : ℤ)) (by simp) hnot w (w + (i + 1)) (by omega)
    rw [Nat.add_sub_cancel_left] at hps
    have hne : (1 + (l : ℤ)) ^ (w + (i + 1)) - (1 + (l : ℤ)) ^ w ≠ 0 := by
      intro h; rw [h, padicValInt.zero] at hps; omega
    have hu0 : -u ≠ 0 := by
      intro h; exact hu (by rw [neg_eq_zero.mp h]; exact dvd_zero _)
    rw [hrw]
    refine ⟨mul_ne_zero hu0 hne, ?_⟩
    rw [padicValInt.mul hu0 hne, hps, padicValInt.eq_zero_of_not_dvd (by rwa [dvd_neg])]
    ring
  have hclaim : ∀ s : ℕ,
      (∏ i ∈ range s, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)))) ≠ 0 ∧
      padicValInt l (∏ i ∈ range s, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)))) =
        s + padicValNat l s.factorial := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [prod_range_succ]
      refine ⟨mul_ne_zero ih.1 (hF s).1, ?_⟩
      rw [padicValInt.mul ih.1 (hF s).1, ih.2, (hF s).2, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero s) (Nat.factorial_ne_zero s)]
      ring
  unfold delta
  rw [prod_erase_zero]
  simp only [Fin.val_succ, Fin.val_zero, add_zero]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) t]
  exact (hclaim t).2

theorem deltaValLe : StatDeltaValLe := by
  intro l hl hl2 u hu w t
  rw [deltaVal l hl2 u hu w t]
  have := padicValNat_factorial_le (p := l) t
  omega

end Formalism.NG
