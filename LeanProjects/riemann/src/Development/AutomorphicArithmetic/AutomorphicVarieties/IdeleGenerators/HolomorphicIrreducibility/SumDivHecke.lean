import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UnitForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.CuspOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EigLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EPrim

open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private theorem sum_div_split (g : ℕ → ℂ) (hg : ∀ a b, g (a * b) = g a * g b) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (p * n).divisors with p ∣ j, g j = g p * ∑ j ∈ n.divisors, g j := by
  have hp0 : 0 < p := hp.pos
  rw [Finset.mul_sum]
  simp_rw [← hg]
  symm
  rw [← Finset.sum_image (g := fun j => p * j) (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h)]
  congr 1
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨a, ⟨ha, hn0⟩, rfl⟩
    exact ⟨⟨mul_dvd_mul_left p ha, Nat.mul_ne_zero hp.ne_zero hn0⟩, dvd_mul_right p a⟩
  · rintro ⟨⟨hj, hpn⟩, ⟨b, rfl⟩⟩
    exact ⟨b, ⟨Nat.dvd_of_mul_dvd_mul_left hp0 hj, by omega⟩, rfl⟩

private theorem sum_div_hecke (g : ℕ → ℂ) (hg : ∀ a b, g (a * b) = g a * g b) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (p * n).divisors, g j + g p * (if p ∣ n then ∑ j ∈ (n / p).divisors, g j else 0) =
      (1 + g p) * ∑ j ∈ n.divisors, g j := by
  have hn0 : n ≠ 0 := by omega
  rw [← Finset.sum_filter_add_sum_filter_not (p * n).divisors (fun j => p ∣ j), sum_div_split g hg hp n hn]
  have hB : ∑ j ∈ (p * n).divisors with ¬p ∣ j, g j = ∑ j ∈ n.divisors with ¬p ∣ j, g j := by
    congr 1
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hj, _⟩, hpj⟩
      have hc : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpj).symm
      exact ⟨⟨hc.dvd_of_dvd_mul_left hj, hn0⟩, hpj⟩
    · rintro ⟨⟨hj, _⟩, hpj⟩
      exact ⟨⟨Dvd.dvd.mul_left hj p, Nat.mul_ne_zero hp.ne_zero hn0⟩, hpj⟩
  have hC : ∑ j ∈ n.divisors, g j = ∑ j ∈ n.divisors with ¬p ∣ j, g j +
      (if p ∣ n then g p * ∑ j ∈ (n / p).divisors, g j else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun j => p ∣ j), add_comm]
    congr 1
    split_ifs with h
    · obtain ⟨m, rfl⟩ := h
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · simp [h0] at hn0
        · exact h0
      rw [Nat.mul_div_cancel_left m hp.pos]
      exact sum_div_split g hg hp m hm
    · apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Nat.mem_divisors] at hj
      exact absurd (hj.2.trans hj.1.1) h
  rw [hB]
  split_ifs at hC ⊢
  · linear_combination (-1 : ℂ) * hC
  · linear_combination (-1 : ℂ) * hC

private theorem sig_hecke (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    sigChi k χ (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then sigChi k χ (n / p) else 0) =
      (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) * sigChi k χ n := by
  have h := sum_div_hecke (fun j => χ (j : ZMod N) * (j : ℂ) ^ (k - 1))
    (by intro a b; push_cast; rw [map_mul, mul_pow]; ring) hp n hn
  simpa only [sigChi] using h

section Int

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private theorem int_add {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x + y)‖ ≤ 1 := by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

private theorem int_sub {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x - y)‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact int_add ι hx (by rwa [map_neg, norm_neg])

private theorem int_mul {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x * y)‖ ≤ 1 := by
  rw [map_mul, norm_mul]
  exact mul_le_one₀ hx (norm_nonneg _) hy

private theorem small_mul {x y : ℂ} (hx : ‖ι.symm x‖ < 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x * y)‖ < 1 := by
  rw [map_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans_lt hx

private theorem int_chi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a : ZMod N) : ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · have hm : χ a ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← ha.unit_spec, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h1 : ‖ι.symm (χ a)‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← norm_pow, ← map_pow, hm, map_one, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h1).le
  · rw [MulChar.map_nonunit χ ha, map_zero, norm_zero]
    exact zero_le_one

private theorem int_term (k : ℕ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (j : ℕ) :
    ‖ι.symm (χ (j : ZMod N) * (j : ℂ) ^ (k - 1))‖ ≤ 1 := by
  refine int_mul ι (int_chi ι χ _) ?_
  rw [map_pow, map_natCast, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ j)

private theorem int_sig (k : ℕ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖ι.symm (sigChi k χ n)‖ ≤ 1 := by
  unfold sigChi
  exact Finset.sum_induction _ (fun x => ‖ι.symm x‖ ≤ 1) (fun a b ha hb => int_add ι ha hb)
    (by simp) (fun j _ => int_term ι k χ j)

end Int

private theorem chi_neg_one {l M w : ℕ} (hl : l.Prime) {φ θ χ} (h : EDat l M w φ θ χ) : χ (-1) = φ (-1) := by
  have hM := h.one_lt
  have hw := h.prime.pos
  have h1 : 1 ≤ M * w := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have key := h.mul (M * w - 1)
  have e1 : ((M * w - 1 : ℕ) : ZMod (M * w)) = -1 := by
    rw [Nat.cast_sub h1, ZMod.natCast_self]; simp
  have e2 : ((M * w - 1 : ℕ) : ZMod M) = -1 := by
    rw [Nat.cast_sub h1, Nat.cast_mul, ZMod.natCast_self]; simp
  have e3 : ((M * w - 1 : ℕ) : ZMod w) = -1 := by
    rw [Nat.cast_sub h1, Nat.cast_mul, ZMod.natCast_self]; simp
  rw [e1, e2, e3] at key
  have hθ : θ (-1) = 1 := by
    have hsq : θ (-1) ^ 2 = 1 := by
      rw [← map_pow]; simp
    have hθl : θ (-1) ^ l = 1 := by
      rw [← MulChar.pow_apply' θ hl.ne_zero, h.θpow, MulChar.one_apply isUnit_one.neg]
    obtain ⟨m, hm⟩ := Nat.Prime.odd_of_ne_two hl h.odd
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at hθl
    exact hθl
  rw [key, hθ, mul_one]

private theorem coef_comb {N k : ℕ} [NeZero N] (E G : ModularForm (Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ) :
    coef (E - c • G : ModularForm (Gamma1 N) (k : ℤ)) n = coef E n - c * coef G n := by
  have h1 : (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  unfold coef
  rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1 E (c • G), ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos h1 c G]
  simp

private theorem slash_comb (k : ℕ) (E G : ℍ → ℂ) (c : ℂ) (γ : SL(2, ℤ)) :
    (E - c • G) ∣[(k : ℤ)] γ = E ∣[(k : ℤ)] γ - c • G ∣[(k : ℤ)] γ := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.SL_smul_slash, ← sub_eq_add_neg]

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.propE :
    UpperTheory.V.Sd.PropE := by
  intro l _ ι M w φ θ χ h
  have hl : l.Prime := Fact.out
  have hM := h.one_lt
  have hw2 := h.prime.two_le
  haveI : NeZero (M * w) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hN3 : 3 ≤ M * w := by nlinarith
  have hlN : ¬ l ∣ M * w := by
    intro hd
    rcases (Nat.Prime.dvd_mul hl).1 hd with h' | h'
    · exact h.cop h'
    · rcases Nat.Prime.eq_one_or_self_of_dvd h.prime l h' with h1 | h1
      · exact hl.one_lt.ne' h1
      · have hs : l ∣ w - (w - 1) := Nat.dvd_sub h' h.dvd
        have hw1 : w - (w - 1) = 1 := by omega
        rw [hw1] at hs
        exact hl.one_lt.ne' (Nat.dvd_one.1 hs)
  obtain ⟨k₁, hk₁⟩ := unitForm l h.odd ι (M * w) hN3 hlN
  refine ⟨max k₁ 3, fun k hk hφ => ?_⟩
  have hk1 : k₁ ≤ k := le_of_max_le_left hk
  have hk3 : 3 ≤ k := le_of_max_le_right hk
  have hχ : χ (-1) = (-1) ^ k := (chi_neg_one hl h).trans hφ
  obtain ⟨G, hGc, hGi, hGv, hG0⟩ := hk₁ k hk1 χ hχ
  obtain ⟨E, hEc, hEv, hEn, hE0⟩ := eisChi (M * w) k (by omega) hk3 χ (ePrim l M w φ θ χ h) hχ
  have hc : ‖ι.symm (coef E 0)‖ < 1 := constSmall l ι M w φ θ χ h k (by omega) _ hE0
  set c := coef (⇑E) 0 with hc_def
  have hF0 : coef (⇑(E - c • G)) 0 = 0 := by
    rw [coef_comb, hG0, mul_one, sub_self]
  have hFc : HasChar k χ ⇑(E - c • G) := by
    intro γ hγ
    rw [ModularForm.coe_sub, ModularForm.coe_smul, slash_comb, hEc γ hγ, hGc γ hγ, smul_sub, smul_comm c]
  have hFv : VanOff (M * w) k ⇑(E - c • G) := by
    intro γ hγ
    rw [ModularForm.coe_sub, ModularForm.coe_smul, slash_comb]
    have ht := (hEv γ hγ).sub ((hGv γ hγ).smul c)
    rw [sub_zero] at ht
    exact ht
  obtain ⟨f, hf⟩ := cuspOf (M * w) k χ (E - c • G) hFc hFv hF0
  have hcf : ∀ m, 1 ≤ m → coef (⇑f) m = sigChi k χ m - c * coef (⇑G) m := by
    intro m hm
    rw [hf, coef_comb, hEn m hm]
  have hfc : HasChar k χ ⇑f := by rw [hf]; exact hFc
  have hInt : IntQ ι ⇑f := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hf, hF0, map_zero, norm_zero]
      exact zero_le_one
    · rw [hcf n hn]
      exact int_sub ι (int_sig ι k χ n) (int_mul ι hc.le (hGi n))
  have hOne : ‖ι.symm (coef (⇑f) 1)‖ = 1 := by
    have hy := small_mul ι hc (hGi 1)
    have hs1 : sigChi k χ 1 = 1 := by simp [sigChi]
    rw [hcf 1 le_rfl, hs1]
    refine le_antisymm (int_sub ι (by simp) hy.le) ?_
    have hmax := IsUltrametricDist.norm_add_le_max (ι.symm (1 - c * coef (⇑G) 1)) (ι.symm (c * coef (⇑G) 1))
    rw [← map_add, sub_add_cancel, map_one, norm_one] at hmax
    rcases le_max_iff.1 hmax with h' | h'
    · exact h'
    · exact absurd h' (not_le.2 hy)
  have hA : ∀ p : ℕ, p.Prime →
      ‖ι.symm (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1))‖ ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n →
        ‖ι.symm ((coef (⇑f) (p * n) + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then coef (⇑f) (n / p) else 0)) -
          (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)) * coef (⇑f) n)‖ < 1 := by
    intro p hp
    have ha : ‖ι.symm (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1))‖ ≤ 1 :=
      int_add ι (by simp) (int_term ι k χ p)
    refine ⟨ha, fun n hn => ?_⟩
    have hs := sig_hecke k χ hp n hn
    have hpn : 1 ≤ p * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hp.ne_zero (by omega))
    have key : (coef (⇑f) (p * n) + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then coef (⇑f) (n / p) else 0)) -
          (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)) * coef (⇑f) n =
        -(c * ((coef (⇑G) (p * n) + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then coef (⇑G) (n / p) else 0)) -
          (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)) * coef (⇑G) n)) := by
      split_ifs at hs ⊢ with hd
      · have hnp : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
        rw [hcf _ hpn, hcf _ hnp, hcf _ hn]
        linear_combination hs
      · rw [hcf _ hpn, hcf _ hn]
        linear_combination hs
    rw [key, map_neg, norm_neg]
    refine small_mul ι hc (int_sub ι (int_add ι (hGi _) (int_mul ι (int_term ι k χ p) ?_)) (int_mul ι ha (hGi n)))
    split_ifs
    · exact hGi _
    · simp
  obtain ⟨g, hg⟩ := eigLift l ι (M * w) k (by omega) χ f hfc hInt hOne
    (fun p => 1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)) hA
  exact ⟨g, hg⟩
