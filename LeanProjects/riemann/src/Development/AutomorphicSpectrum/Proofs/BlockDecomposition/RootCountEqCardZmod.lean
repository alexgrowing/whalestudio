import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Finset

namespace GlobalTheory.CompanionTheory.SquareRootCount

def rootCount (n : ℤ) (e : ℕ) : ℕ :=
  ((range e).filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card

noncomputable def addCharAt (d : ℕ) (t : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (d : ℂ))

noncomputable def rootSum (n : ℤ) (d : ℕ) : ℂ :=
  ∑ x ∈ range d, ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d),
    addCharAt d ((r : ℤ) * ((x : ℤ) ^ 2 - n))

theorem geom_addChar {e : ℕ} (he : 0 < e) (m : ℤ) :
    ∑ r ∈ range e, addCharAt e ((r : ℤ) * m) = if (e : ℤ) ∣ m then (e : ℂ) else 0 := by
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (e : ℂ))) e :=
    Complex.isPrimitiveRoot_exp e he.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (e : ℂ)) with hζ
  have hterm : ∀ r : ℕ, addCharAt e ((r : ℤ) * m) = (ζ ^ m) ^ r := by
    intro r
    rw [← zpow_natCast, ← zpow_mul, hζ, ← Complex.exp_int_mul]
    unfold addCharAt
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  split_ifs with h
  · rw [(hprim.zpow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hprim.zpow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1]
    have : (ζ ^ m) ^ e = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    simp [this]

theorem count_periodic (n : ℤ) (e k : ℕ) :
    ((range (e * k)).filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card = k * rootCount n e := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : ∀ s : Finset ℕ, (s.filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card
        = ∑ x ∈ s, if (e : ℤ) ∣ (x : ℤ) ^ 2 - n then 1 else 0 := fun s => by
      rw [card_filter]
    rw [hs] at ih ⊢
    rw [Nat.mul_succ, sum_range_add, ih, Nat.succ_mul]
    congr 1
    unfold rootCount
    rw [hs]
    refine sum_congr rfl fun x _ => ?_
    have : (e : ℤ) ∣ (((e * k + x : ℕ) : ℤ)) ^ 2 - n ↔ (e : ℤ) ∣ (x : ℤ) ^ 2 - n := by
      have hd : (e : ℤ) ∣ (((e * k + x : ℕ) : ℤ)) ^ 2 - (x : ℤ) ^ 2 :=
        ⟨k * (e * k + 2 * x), by push_cast; ring⟩
      constructor
      · intro h
        have := dvd_sub h hd
        simpa using this
      · intro h
        have := dvd_add h hd
        simpa using this
    simp only [this]

theorem sum_moebius_divisors {m : ℕ} (hm : m ≠ 0) :
    ∑ g ∈ m.divisors, ArithmeticFunction.moebius g = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

theorem sum_coprime_eq {d : ℕ} (hd : 0 < d) (f : ℕ → ℂ) :
    ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d), f r
      = ∑ g ∈ d.divisors, (ArithmeticFunction.moebius g : ℂ) * ∑ r ∈ range (d / g), f (g * r) := by
  have hind : ∀ r : ℕ, (if Nat.Coprime r d then f r else 0)
      = ∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) * f r else 0 := by
    intro r
    have hg : Nat.gcd r d ≠ 0 := Nat.gcd_ne_zero_right hd.ne'
    have hdiv : (Nat.gcd r d).divisors = d.divisors.filter (· ∣ r) := by
      ext g
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩
        exact ⟨⟨h2, hd.ne'⟩, h1⟩
      · rintro ⟨⟨h2, -⟩, h1⟩
        exact ⟨⟨h1, h2⟩, hg⟩
    have h := sum_moebius_divisors hg
    rw [hdiv, sum_filter] at h
    have h' : (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) else 0)
        = if Nat.Coprime r d then 1 else 0 := by
      have := congrArg (fun z : ℤ => (z : ℂ)) h
      simp only [Int.cast_sum] at this
      simp only [apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, Int.cast_one] at this
      exact this
    have h'' : (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) * f r else 0)
        = (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) else 0) * f r := by
      rw [sum_mul]
      refine sum_congr rfl fun g _ => ?_
      split_ifs <;> simp
    rw [h'', h']
    split_ifs <;> simp
  rw [sum_filter]
  simp_rw [hind]
  rw [sum_comm]
  refine sum_congr rfl fun g hg => ?_
  have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  rw [← sum_filter, ← mul_sum]
  congr 1
  have himg : (range d).filter (fun r => g ∣ r) = (range (d / g)).image (fun r => g * r) := by
    ext r
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hr, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      rw [Nat.lt_div_iff_mul_lt' hgd]
      exact hr
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      rwa [Nat.lt_div_iff_mul_lt' hgd] at hk
  rw [himg, sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hg0 hab

theorem addCharAt_mul {g e : ℕ} (hg : 0 < g) (he : 0 < e) (t : ℤ) :
    addCharAt (g * e) ((g : ℤ) * t) = addCharAt e t := by
  unfold addCharAt
  congr 1
  have h1 : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have h2 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  push_cast
  field_simp

theorem rootSum_eq (n : ℤ) {d : ℕ} (hd : 0 < d) :
    rootSum n d
      = (d : ℂ) * ∑ e ∈ d.divisors, (ArithmeticFunction.moebius (d / e) : ℂ) * (rootCount n e : ℂ) := by
  have hinner : ∀ x : ℕ, ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d),
      addCharAt d ((r : ℤ) * ((x : ℤ) ^ 2 - n))
      = ∑ g ∈ d.divisors, (ArithmeticFunction.moebius g : ℂ) *
          (if ((d / g : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - n then ((d / g : ℕ) : ℂ) else 0) := by
    intro x
    rw [sum_coprime_eq hd]
    refine sum_congr rfl fun g hg => ?_
    have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
    have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
    have he : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hg0
    congr 1
    rw [← geom_addChar he]
    refine sum_congr rfl fun r _ => ?_
    conv_lhs => rw [← Nat.mul_div_cancel' hgd]
    rw [← addCharAt_mul hg0 he]
    congr 1
    push_cast
    ring
  unfold rootSum
  simp_rw [hinner]
  rw [sum_comm]
  rw [← Nat.sum_div_divisors d (fun e => (ArithmeticFunction.moebius (d / e) : ℂ) * (rootCount n e : ℂ)), mul_sum]
  refine sum_congr rfl fun g hg => ?_
  have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  have he : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hg0
  rw [← mul_sum, Nat.div_div_self hgd hd.ne']
  have hcount : ∑ x ∈ range d, (if ((d / g : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - n then ((d / g : ℕ) : ℂ) else 0)
      = ((d / g : ℕ) : ℂ) * ((g : ℂ) * (rootCount n (d / g) : ℂ)) := by
    have hc := count_periodic n (d / g) g
    rw [Nat.div_mul_cancel hgd] at hc
    rw [← sum_filter, sum_const, nsmul_eq_mul, hc]
    push_cast
    ring
  rw [hcount]
  have hdc : (d : ℂ) = ((d / g : ℕ) : ℂ) * (g : ℂ) := by
    exact_mod_cast (Nat.div_mul_cancel hgd).symm
  rw [hdc]
  ring

theorem rootCount_eq_card_zmod (n : ℤ) (e : ℕ) [NeZero e] :
    rootCount n e = (univ.filter fun x : ZMod e => x ^ 2 = (n : ZMod e)).card := by
  have key : ∀ x : ℕ, (e : ℤ) ∣ (x : ℤ) ^ 2 - n ↔ ((x : ZMod e)) ^ 2 = (n : ZMod e) := by
    intro x
    rw [← CharP.intCast_eq_zero_iff (ZMod e) e]
    push_cast
    exact sub_eq_zero
  unfold rootCount
  refine card_bij (fun x _ => (x : ZMod e)) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and]
    exact (key x).1 (mem_filter.1 hx).2
  · intro a ha b hb hab
    have ha' := mem_range.1 (mem_filter.1 ha).1
    have hb' := mem_range.1 (mem_filter.1 hb).1
    have := (ZMod.natCast_eq_natCast_iff' a b e).1 hab
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  · intro y hy
    refine ⟨y.val, ?_, by simp⟩
    refine mem_filter.2 ⟨mem_range.2 (ZMod.val_lt y), (key _).2 ?_⟩
    simpa using (mem_filter.1 hy).2

theorem rr_eq_rootSum (n : ℤ) (d : ℕ) : Ad3.S.RR n d = rootSum n d := by
  unfold Ad3.S.RR rootSum Ad3.S.GS
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun r _ => ?_
  unfold Ad3.S.ee addCharAt
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rr_eq : Ad3.S.N1 := fun n d hd => by
  rw [rr_eq_rootSum]
  exact rootSum_eq n hd

end GlobalTheory.CompanionTheory.SquareRootCount
