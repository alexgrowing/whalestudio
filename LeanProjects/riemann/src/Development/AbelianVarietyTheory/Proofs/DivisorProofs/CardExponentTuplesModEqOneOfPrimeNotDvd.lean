import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.ExpCount

theorem eq_zero_of_modEq (q l m k c : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hm : 0 < m) (hlm : ¬ l ∣ m)
    (hreg : Reg q m k) (hc : c < l * m) (hlc : l ∣ c)
    (h : k * (∑ i ∈ Finset.range l, q ^ (m * i)) * q ^ c ≡ k * ∑ i ∈ Finset.range l, q ^ (m * i)
      [MOD q ^ (l * m) - 1]) : c = 0 := by
  set S : ℕ := ∑ i ∈ Finset.range l, q ^ (m * i) with hS
  have hSpos : 0 < S := Finset.sum_pos (fun i _ => by positivity) ⟨0, Finset.mem_range.2 hl.pos⟩
  have hgeom : ((q ^ (l * m) - 1 : ℕ) : ℤ) = ((q : ℤ) ^ m - 1) * (S : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), hS]
    push_cast
    have e : ∑ i ∈ Finset.range l, (q : ℤ) ^ (m * i) = ∑ i ∈ Finset.range l, ((q : ℤ) ^ m) ^ i :=
      Finset.sum_congr rfl fun i _ => by rw [pow_mul]
    rw [e, mul_comm ((q : ℤ) ^ m - 1), geom_sum_mul, ← pow_mul, mul_comm m l]
  have h1 := Nat.modEq_iff_dvd.1 h
  rw [hgeom] at h1
  push_cast at h1
  have h2 : ((q : ℤ) ^ m - 1) ∣ (k : ℤ) - k * (q : ℤ) ^ c := by
    have h1' : ((q : ℤ) ^ m - 1) * S ∣ ((k : ℤ) - k * (q : ℤ) ^ c) * S := by
      convert h1 using 1; ring
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hSpos.ne')).1 h1'
  have h3 : ((q : ℤ) ^ m - 1) ∣ (k : ℤ) - k * (q : ℤ) ^ (c % m) := by
    have hc' : (q : ℤ) ^ c = ((q : ℤ) ^ m) ^ (c / m) * (q : ℤ) ^ (c % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have e : (k : ℤ) - k * (q : ℤ) ^ (c % m) = ((k : ℤ) - k * (q : ℤ) ^ c)
        + k * (q : ℤ) ^ (c % m) * (((q : ℤ) ^ m) ^ (c / m) - 1 ^ (c / m)) := by
      rw [hc']; ring
    rw [e]
    exact dvd_add h2 (Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ _) _)
  have hmc : m ∣ c := by
    by_contra hne
    have hd : 0 < c % m := Nat.pos_of_ne_zero (fun h0 => hne (Nat.dvd_of_mod_eq_zero h0))
    apply hreg (c % m) hd (Nat.mod_lt c hm)
    apply Nat.modEq_iff_dvd.2
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    push_cast
    exact h3
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  exact Nat.eq_zero_of_dvd_of_lt (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hlc hmc) hc

theorem pow_val_add_natCast {M N : ℕ} [NeZero N] (Q : ZMod M) (hQ : Q ^ N = 1) (x : ZMod N) (n : ℕ) :
    Q ^ (x + (n : ZMod N)).val = Q ^ x.val * Q ^ n := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + n) N, pow_add, pow_mul, hQ, one_pow, mul_one]

theorem fixed_eq (l' m : ℕ) (hl : (l' + 1).Prime) (hlm : ¬ (l' + 1) ∣ m)
    (h : ZMod (l' + 1) → ZMod ((l' + 1) * m)) (hfix : ∀ r, h (r - m) + m = h r) (r : ZMod (l' + 1)) :
    h r = h 0 + (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) := by
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have hind : ∀ n : ℕ, h ((n : ZMod (l' + 1)) * m) = h 0 + ((n * m : ℕ) : ZMod ((l' + 1) * m)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hf := hfix (((n + 1 : ℕ) : ZMod (l' + 1)) * m)
      rw [← hf]
      have e : ((n + 1 : ℕ) : ZMod (l' + 1)) * m - m = (n : ZMod (l' + 1)) * m := by push_cast; ring
      rw [e, ih]; push_cast; ring
  have hr : r = (((r * (m : ZMod (l' + 1))⁻¹).val : ℕ) : ZMod (l' + 1)) * m := by
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
  conv_lhs => rw [hr]
  exact hind _

theorem fixed_sum (M l' m : ℕ) (Q : ZMod M) (hl : (l' + 1).Prime) (hlm : ¬ (l' + 1) ∣ m) (hm : 0 < m)
    (hQ : Q ^ ((l' + 1) * m) = 1)
    (h : ZMod (l' + 1) → ZMod ((l' + 1) * m)) (hfix : ∀ r, h (r - m) + m = h r) :
    ∑ r, Q ^ (h r).val = Q ^ (h 0).val * ∑ i ∈ Finset.range (l' + 1), Q ^ (m * i) := by
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  rw [Finset.sum_congr rfl (fun r _ => by rw [fixed_eq l' m hl hlm h hfix r, pow_val_add_natCast Q hQ]),
    ← Finset.mul_sum]
  congr 1
  have e1 : ∑ r : ZMod (l' + 1), Q ^ ((r * (m : ZMod (l' + 1))⁻¹).val * m)
      = ∑ s : ZMod (l' + 1), Q ^ (s.val * m) :=
    Equiv.sum_comp (Equiv.mulRight₀ ((m : ZMod (l' + 1))⁻¹) (inv_ne_zero hm0)) (fun s : ZMod (l' + 1) => Q ^ (s.val * m))
  rw [e1, ← Fin.sum_univ_eq_sum_range (fun i => Q ^ (m * i)) (l' + 1)]
  exact Finset.sum_congr rfl fun s _ => by rw [mul_comm]; rfl

end GlobalTheory.ExpCount

namespace GlobalTheory.ExpCount

theorem card_eq (q l' m k : ℕ) (hm : 0 < m) :
    (Finset.univ.filter fun a : Fin (l' + 1) → Fin m => k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) ≡
      ∑ j : Fin (l' + 1), k * q ^ (j : ℕ) * (q ^ (l' + 1)) ^ (a j : ℕ) [MOD (q ^ (l' + 1)) ^ m - 1]).card =
    Nat.card {g : ZMod (l' + 1) → ZMod ((l' + 1) * m) //
      (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) ∧
      ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod (q ^ ((l' + 1) * m) - 1)) =
        ∑ r, (k : ZMod (q ^ ((l' + 1) * m) - 1)) * (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (g r).val} := by
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  let ef : Fin (l' + 1) ≃ ZMod (l' + 1) := Equiv.refl _
  have hef : ∀ r : ZMod (l' + 1), ((ef.symm r : Fin (l' + 1)) : ℕ) = r.val := fun r => rfl
  have hef' : ∀ j : Fin (l' + 1), (ef j).val = (j : ℕ) := fun j => rfl
  have hb : ∀ (j : ℕ) (x : ℕ), j < l' + 1 → x < m → j + (l' + 1) * x < (l' + 1) * m := by
    intro j x hj hx
    calc j + (l' + 1) * x < (l' + 1) + (l' + 1) * x := by omega
      _ = (l' + 1) * (x + 1) := by ring
      _ ≤ (l' + 1) * m := Nat.mul_le_mul_left _ hx
  have hkey : ∀ (g : ZMod (l' + 1) → ZMod ((l' + 1) * m)),
      (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) →
      ∀ r : ZMod (l' + 1), r.val + (l' + 1) * ((g r).val / (l' + 1)) = (g r).val := by
    intro g hg r
    have h := hg r
    rw [ZMod.castHom_apply, ← ZMod.natCast_val] at h
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_natCast] at h2
    rw [← h2, Nat.mod_add_div]
  have hmod : (q ^ (l' + 1)) ^ m - 1 = q ^ ((l' + 1) * m) - 1 := by rw [← pow_mul]
  refine Nat.card_congr
    { toFun := fun a => ⟨fun r => ((r.val + (l' + 1) * (a.1 (ef.symm r)).val : ℕ) : ZMod ((l' + 1) * m)), ?_, ?_⟩
      invFun := fun g => ⟨fun j => ⟨(g.1 (ef j)).val / (l' + 1),
        (Nat.div_lt_iff_lt_mul (Nat.succ_pos l')).2 (lt_of_lt_of_eq (ZMod.val_lt _) (mul_comm _ _))⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro r
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]
  · rcases a with ⟨a, ha⟩
    rw [hmod] at ha
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 ha
    have hv : ∀ r : ZMod (l' + 1), (((r.val + (l' + 1) * (a (ef.symm r)).val : ℕ) : ZMod ((l' + 1) * m))).val
        = r.val + (l' + 1) * (a (ef.symm r)).val := fun r =>
      ZMod.val_cast_of_lt (hb _ _ (ZMod.val_lt r) (a (ef.symm r)).isLt)
    simp only [hv]
    rw [h]; push_cast
    rw [← Equiv.sum_comp ef.symm (fun j : Fin (l' + 1) => (k : ZMod (q ^ ((l' + 1) * m) - 1)) *
      (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (j : ℕ) * ((q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (l' + 1)) ^ (a j : ℕ))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pow_add (q : ZMod (q ^ ((l' + 1) * m) - 1)) r.val, hef, mul_assoc, ← pow_mul]
  · rcases g with ⟨g, hg1, hg2⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    show ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod ((q ^ (l' + 1)) ^ m - 1)) =
      ((∑ j : Fin (l' + 1), k * q ^ (j : ℕ) * (q ^ (l' + 1)) ^ ((g (ef j)).val / (l' + 1)) : ℕ) : ZMod ((q ^ (l' + 1)) ^ m - 1))
    rw [hmod, hg2]; push_cast
    rw [← Equiv.sum_comp ef (fun r : ZMod (l' + 1) => (k : ZMod (q ^ ((l' + 1) * m) - 1)) *
      (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (g r).val)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_assoc, ← pow_add, ← hef' j, hkey g hg1 (ef j)]
  · intro a
    apply Subtype.ext; funext j; apply Fin.ext
    show ((((ef j).val + (l' + 1) * (a.1 (ef.symm (ef j))).val : ℕ) : ZMod ((l' + 1) * m))).val / (l' + 1)
      = (a.1 j).val
    rw [Equiv.symm_apply_apply, ZMod.val_cast_of_lt (hb _ _ (ZMod.val_lt _) (a.1 j).isLt),
      Nat.add_mul_div_left _ _ (Nat.succ_pos l'), Nat.div_eq_of_lt (ZMod.val_lt _), zero_add]
  · intro g
    apply Subtype.ext; funext r
    show ((r.val + (l' + 1) * ((g.1 (ef (ef.symm r))).val / (l' + 1)) : ℕ) : ZMod ((l' + 1) * m)) = g.1 r
    rw [Equiv.apply_symm_apply, hkey g.1 g.2.1 r, ZMod.natCast_zmod_val]

end GlobalTheory.ExpCount

namespace GlobalTheory.ExpCount

theorem count_one_mod : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k →
    (Finset.univ.filter fun a : Fin l → Fin m => k * ∑ i ∈ Finset.range l, q ^ (m * i) ≡
      ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ m - 1]).card ≡ 1 [MOD l] := by
  intro q l m k hq hl hm hlm hreg
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := hl.one_lt; omega⟩
  rw [card_eq q l' m k hm]
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have hQ : (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ ((l' + 1) * m) = 1 := by
    have h0 : ((q ^ ((l' + 1) * m) - 1 : ℕ) : ZMod (q ^ ((l' + 1) * m) - 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))] at h0
    push_cast at h0
    exact sub_eq_zero.1 h0
  generalize hMdef : q ^ ((l' + 1) * m) - 1 = M at hQ ⊢
  have hSQ : (q : ZMod M) ^ m * ∑ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ (m * i)
      = ∑ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ (m * i) := by
    have h1 := Finset.sum_range_succ' (fun i => (q : ZMod M) ^ (m * i)) (l' + 1)
    have h2 := Finset.sum_range_succ (fun i => (q : ZMod M) ^ (m * i)) (l' + 1)
    beta_reduce at h1 h2
    have h3 : (q : ZMod M) ^ (m * (l' + 1)) = (q : ZMod M) ^ (m * 0) := by
      rw [mul_comm m, hQ, mul_zero, pow_zero]
    rw [h3] at h2
    rw [Finset.mul_sum]
    have h4 : ∀ i ∈ Finset.range (l' + 1),
        (q : ZMod M) ^ m * (q : ZMod M) ^ (m * i) = (q : ZMod M) ^ (m * (i + 1)) := fun i _ => by
      rw [← pow_add]; congr 1; ring
    rw [Finset.sum_congr rfl h4]
    exact add_right_cancel (h1.symm.trans h2)
  let P : (ZMod (l' + 1) → ZMod ((l' + 1) * m)) → Prop := fun g =>
    (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) ∧
      ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M) = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r).val
  have hpres : ∀ g, P g → P (fun r => g (r - m) + m) := by
    intro g hg
    refine ⟨fun r => ?_, ?_⟩
    · rw [map_add, hg.1, map_natCast]; ring
    · have e : ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g (r - m) + m).val
          = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r + m).val :=
        Equiv.sum_comp (Equiv.subRight (m : ZMod (l' + 1))) (fun r => (k : ZMod M) * (q : ZMod M) ^ (g r + m).val)
      show _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g (r - m) + m).val
      rw [e]
      calc ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M)
          = (q : ZMod M) ^ m * ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M) := by
            push_cast; rw [mul_left_comm, hSQ]
        _ = (q : ZMod M) ^ m * ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r).val := by rw [hg.2]
        _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r + m).val := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [pow_val_add_natCast _ hQ]; ring
  let X := {g : ZMod (l' + 1) → ZMod ((l' + 1) * m) // P g}
  let σ : Function.End X := fun g => ⟨fun r => g.1 (r - m) + m, hpres g.1 g.2⟩
  have hpow : ∀ n : ℕ, ∀ g : X, ((σ ^ n) g).1 =
      fun r => g.1 (r - (n : ZMod (l' + 1)) * m) + ((n * m : ℕ) : ZMod ((l' + 1) * m)) := by
    intro n
    induction n with
    | zero => intro g; funext r; rw [pow_zero]; show g.1 r = _; simp
    | succ n ih =>
      intro g; funext r
      rw [pow_succ]
      show ((σ ^ n) (σ g)).1 r = _
      rw [ih]
      show g.1 (r - (n : ZMod (l' + 1)) * m - m) + m + ((n * m : ℕ) : ZMod ((l' + 1) * m)) = _
      rw [add_assoc]
      congr 1
      · congr 1; push_cast; ring_nf
      · push_cast; ring
  have hσ : σ ^ (l' + 1) ^ 1 = 1 := by
    rw [pow_one]
    refine funext fun g => Subtype.ext ?_
    rw [hpow]
    funext r
    show _ = g.1 r
    rw [ZMod.natCast_self, ZMod.natCast_self, zero_mul, sub_zero, add_zero]
  have hcard := Equiv.Perm.card_fixedPoints_modEq (p := l' + 1) (n := 1) hσ
  let gs : ZMod (l' + 1) → ZMod ((l' + 1) * m) :=
    fun r => (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m))
  have hgs_fix : ∀ r, gs (r - m) + m = gs r := by
    intro r
    show ((((r - m) * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) + m
      = (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m))
    have e : (r - m) * (m : ZMod (l' + 1))⁻¹ = r * (m : ZMod (l' + 1))⁻¹ - 1 := by
      rw [sub_mul, mul_inv_cancel₀ hm0]
    rw [e]
    have h1 : (r * (m : ZMod (l' + 1))⁻¹ - 1).val + 1 ≡ (r * (m : ZMod (l' + 1))⁻¹).val [MOD l' + 1] := by
      rw [← ZMod.natCast_eq_natCast_iff]; push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.mul_right' m h1)
    rw [← h2]; push_cast; ring
  have hgs0 : gs 0 = 0 := by simp [gs]
  have hgsP : P gs := by
    refine ⟨fun r => ?_, ?_⟩
    · show ZMod.castHom _ (ZMod (l' + 1)) (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) = r
      rw [map_natCast]; push_cast
      rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
    · show _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (gs r).val
      rw [← Finset.mul_sum, fixed_sum M l' m _ hl hlm hm hQ gs hgs_fix, hgs0, ZMod.val_zero, pow_zero, one_mul]
      push_cast; rfl
  have huniq : ∀ g, P g → (∀ r, g (r - m) + m = g r) → g = gs := by
    intro g hg hfix
    have hs := fixed_sum M l' m (q : ZMod M) hl hlm hm hQ g hfix
    have hlc : l' + 1 ∣ (g 0).val := by
      have h := hg.1 0
      rw [ZMod.castHom_apply, ← ZMod.natCast_val] at h
      exact (ZMod.natCast_eq_zero_iff _ _).1 h
    have hmodeq : k * (∑ i ∈ Finset.range (l' + 1), q ^ (m * i)) * q ^ (g 0).val
        ≡ k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) [MOD q ^ ((l' + 1) * m) - 1] := by
      rw [hMdef, ← ZMod.natCast_eq_natCast_iff]
      have h2 := hg.2
      rw [← Finset.mul_sum, hs] at h2
      push_cast at h2 ⊢
      linear_combination h2.symm
    have hc := eq_zero_of_modEq q (l' + 1) m k (g 0).val hq hl hm hlm hreg (ZMod.val_lt _) hlc hmodeq
    have h0 : g 0 = 0 := (ZMod.val_eq_zero _).1 hc
    funext r
    rw [fixed_eq l' m hl hlm g hfix r, h0, zero_add]
  have hfp : Fintype.card (Function.fixedPoints σ) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨gs, hgsP⟩, ?_⟩, ?_⟩
    · show σ ⟨gs, hgsP⟩ = ⟨gs, hgsP⟩
      exact Subtype.ext (funext hgs_fix)
    · rintro ⟨⟨g, hg⟩, hfx⟩
      have hfx' : σ ⟨g, hg⟩ = ⟨g, hg⟩ := hfx
      have hfix : ∀ r, g (r - m) + m = g r := fun r => congrFun (congrArg Subtype.val hfx') r
      exact Subtype.ext (Subtype.ext (huniq g hg hfix))
  change Nat.card X ≡ 1 [MOD l' + 1]
  rw [Nat.card_eq_fintype_card]
  exact hcard.trans (by rw [hfp])

end GlobalTheory.ExpCount
