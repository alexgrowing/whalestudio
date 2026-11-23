import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropTermSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropHilbWSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

namespace SectionCount.Drop

theorem pow_add_le (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) :
    ∀ e : ℕ, (n + c) ^ e ≤ n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)
  | 0 => by simp
  | e + 1 => by
    have ih := pow_add_le c n hc hn e
    have hn0 : 0 < n := by linarith
    have hA : 0 ≤ (1 + c) ^ e - 1 := by
      have : 1 ≤ (1 + c) ^ e := one_le_pow₀ (by linarith)
      linarith
    have hq : n ^ e / n ≤ n ^ e := div_le_self (by positivity) hn
    have hq' : n ^ (e + 1) / n = n ^ e := by
      rw [pow_succ]; field_simp
    have hqn : n ^ e / n * n = n ^ e := by field_simp
    have h1 : (n + c) ^ e * (n + c) ≤ (n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)) * (n + c) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : ((1 + c) ^ e - 1) * c * (n ^ e / n) ≤ ((1 + c) ^ e - 1) * c * n ^ e :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg hA hc)
    rw [hq', pow_succ, pow_succ, pow_succ]
    nlinarith [h1, h2, hqn]

theorem pow_add_le_mul (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) (e : ℕ) :
    (n + c) ^ e ≤ (1 + c) ^ e * n ^ e := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith) (by nlinarith) e

theorem term_le (I C c n h : ℝ) (e d : ℕ) (hed : e ≤ d) (hc : 0 ≤ c) (hn : 1 ≤ n)
    (hh : |h - I * (n + c) ^ e / (e.factorial : ℝ)| ≤ C * (n + c) ^ e / (n + c)) :
    h ≤ (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) +
      (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) := by
  have hn0 : 0 < n := by linarith
  have hnc : n ≤ n + c := by linarith
  have hP : (n + c) ^ e ≤ (1 + c) ^ e * n ^ e := pow_add_le_mul c n hc hn e
  have hPe : 0 ≤ (n + c) ^ e := by positivity
  have hne : n ^ e ≤ n ^ d := pow_le_pow_right₀ hn hed
  have h1 := (abs_le.mp hh).2

  have hC : C * (n + c) ^ e / (n + c) ≤ |C| * (1 + c) ^ e * (n ^ d / n) := by
    calc C * (n + c) ^ e / (n + c) ≤ |C| * (n + c) ^ e / (n + c) := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * (n + c) ^ e / n := by
          apply div_le_div_of_nonneg_left (by positivity) hn0 hnc
      _ ≤ |C| * ((1 + c) ^ e * n ^ e) / n := by gcongr
      _ ≤ |C| * ((1 + c) ^ e * n ^ d) / n := by gcongr
      _ = |C| * (1 + c) ^ e * (n ^ d / n) := by ring
  have hfac : (1 : ℝ) ≤ (e.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero e)

  have hM : I * (n + c) ^ e / (e.factorial : ℝ) ≤
      (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) + |I| * (1 + c) ^ e * (n ^ d / n) := by
    split_ifs with hde
    · subst hde
      have hA := pow_add_le c n hc hn e
      have hlow : n ^ e ≤ (n + c) ^ e := pow_le_pow_left₀ hn0.le hnc e
      have hD : 0 ≤ (n + c) ^ e - n ^ e := by linarith
      have hq : 0 ≤ n ^ e / n := by positivity
      have hdiff : I * ((n + c) ^ e - n ^ e) ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by
        calc I * ((n + c) ^ e - n ^ e) ≤ |I| * ((n + c) ^ e - n ^ e) :=
              mul_le_mul_of_nonneg_right (le_abs_self I) hD
          _ ≤ |I| * (((1 + c) ^ e - 1) * (n ^ e / n)) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg I)
          _ ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg I)
      have hpos : (0 : ℝ) < (e.factorial : ℝ) := by linarith
      have hR : 0 ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by positivity
      rw [div_le_iff₀ hpos]
      have : I * (n + c) ^ e = I * n ^ e + I * ((n + c) ^ e - n ^ e) := by ring
      rw [this, add_mul, div_mul_cancel₀ _ hpos.ne']
      nlinarith
    · have hlt : e < d := lt_of_le_of_ne hed hde
      have hd1 : n ^ e ≤ n ^ d / n := by
        rw [le_div_iff₀ hn0, ← pow_succ]
        exact pow_le_pow_right₀ hn hlt
      have hpos : (0 : ℝ) < (e.factorial : ℝ) := by linarith
      calc I * (n + c) ^ e / (e.factorial : ℝ) ≤ |I| * (n + c) ^ e / (e.factorial : ℝ) := by
            gcongr; exact le_abs_self I
        _ ≤ |I| * (n + c) ^ e := div_le_self (by positivity) hfac
        _ ≤ |I| * ((1 + c) ^ e * n ^ e) := by gcongr
        _ ≤ |I| * ((1 + c) ^ e * (n ^ d / n)) := by gcongr
        _ = 0 * n ^ d / (d.factorial : ℝ) + |I| * (1 + c) ^ e * (n ^ d / n) := by ring
  have : (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) =
      |I| * (1 + c) ^ e * (n ^ d / n) + |C| * (1 + c) ^ e * (n ^ d / n) := by ring
  rw [this]
  linarith

theorem interNum_fin_congr {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {a a' : ℕ} (h : a = a') (pp : Ideal (Poly S N)) (F : SubSystem S x Ω) :
    interNum pp (fun _ : Fin a => F) = interNum pp (fun _ : Fin a' => F) := by
  subst h; rfl

end SectionCount.Drop

open Classical in

theorem SectionCount.Drop.proof (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨β, hβ, hβZ, m, pp, e, c, hpp, hcount, hloss⟩ := hF k Ω N x d Nb b hZ hb
  choose c' hc' using fun j => hT k Ω N x Nb b (pp j) (e j) (c j) hN (hpp j).1
  choose C hC using fun j => hH k Ω N x Nb (pp j) (e j) hN (hpp j).1
  obtain ⟨-, hsym, -, hcut, -⟩ := hR k Ω N x
  set g : Ideal (Poly k N) → ℤ := fun qq => interNum qq (fun _ : Fin d => Nb.toSubSystem) with hg

  have hkey : ∑ j, (if e j = d then interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) else 0) =
      interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) := by
    have h1 : ∀ j, (if e j = d then interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) else 0) =
        if e j = d then g (pp j) else 0 := fun j => by
      split_ifs with h
      · exact SectionCount.Drop.interNum_fin_congr h _ _
      · rfl
    have hc4 := hcut d (primeOf (S := k) x) (fun _ => Nb) (twistBundle k x (b : ℤ)) β hZ hβ hβZ
    have htb : (twistBundle k x (b : ℤ)).toSubSystem = twistSys k x (b : ℤ) := rfl
    simp only [htb] at hc4
    have hrot := hsym (d + 1) (primeOf (S := k) x)
      (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ)) (fun _ => Nb))
      (finRotate (d + 1)) hZ
    have hL : (fun i => (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ))
        (fun _ => Nb) i).toSubSystem) = Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
          (fun _ : Fin d => Nb.toSubSystem) := by
      funext i; refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; rfl
      · simp only [Fin.cons_succ]
    have hLr : (fun i => (Fin.cons (α := fun _ => LineBundle k x) (twistBundle k x (b : ℤ))
        (fun _ => Nb) (finRotate (d + 1) i)).toSubSystem) =
          Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i : Fin d => ((fun _ => Nb) i).toSubSystem)
            (twistSys k x (b : ℤ)) := by
      funext i; refine Fin.lastCases ?_ (fun i => ?_) i
      · simp; rfl
      · simp [finRotate_apply]
    rw [← hL, ← hrot, hLr, hc4, Finset.sum_congr rfl (fun j _ => h1 j)]
    have hTq : ∀ qq : Ideal (Poly k N),
        (if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
            IsSubvar x qq d then
          haveI : qq.IsPrime := h.1.1.1
          ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ) *
            interNum qq (fun _ : Fin d => Nb.toSubSystem)
        else 0) = ∑ j, if e j = d ∧ pp j = qq then g qq else 0 := by
      intro qq
      have hq := hcount qq
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      by_cases hP : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
          IsSubvar x qq d
      · rw [dif_pos hP]; rw [dif_pos hP] at hq; rw [hq]
      · rw [dif_neg hP]; rw [dif_neg hP] at hq; rw [hq]; simp
    rw [finsum_congr hTq, finsum_eq_sum_of_support_subset (s := Finset.univ.image pp)]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hd : e j = d
      · simp only [hd, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp
      · simp [hd]
    · intro qq hqq
      rw [Function.mem_support] at hqq
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hqq
      have : pp j = qq := by
        by_contra hne; simp [hne] at hj
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨j, this⟩
  have hkeyR : ∑ j, (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0) =
      (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) : ℝ) := by
    rw [← hkey]; push_cast; rfl
  have hev : ∀ᶠ n : ℕ in atTop, ∀ j,
      |(Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c' j) 0)
          ((twistMul Nb.toSubSystem (n + c' j) 0).twist (idealSys x (pp j))) 0) : ℝ) -
        (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) * ((n + c' j : ℕ) : ℝ) ^ (e j) /
          ((e j).factorial : ℝ)| ≤ C j * ((n + c' j : ℕ) : ℝ) ^ (e j) / ((n + c' j : ℕ) : ℝ) := by
    rw [eventually_all]; intro j
    exact (tendsto_add_atTop_nat (c' j)).eventually (hC j)
  refine ⟨∑ j, (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) *
    (1 + (c' j : ℝ)) ^ (e j), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1 i _
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 := (Int.cast_le (R := ℝ)).mpr (hloss n i)
  push_cast at h1
  have h3 : ∀ j, (Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c' j) 0)
      ((twistMul Nb.toSubSystem (n + c' j) 0).twist (idealSys x (pp j))) 0) : ℝ) ≤
      (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0) *
        (n : ℝ) ^ d / (d.factorial : ℝ) +
      (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) * (1 + (c' j : ℝ)) ^ (e j) *
        ((n : ℝ) ^ d / n) := fun j => by
    have hj := hn j
    push_cast at hj
    exact SectionCount.Drop.term_le _ _ _ _ _ (e j) d (hpp j).2.1 (Nat.cast_nonneg _) hn1' hj
  calc _ ≤ _ := h1
    _ ≤ _ := Finset.sum_le_sum (fun j _ => by exact_mod_cast ((hc' j) n i).2)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => h3 j)
    _ = (∑ j, (if e j = d then (interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ) else 0)) *
          (n : ℝ) ^ d / (d.factorial : ℝ) +
        (∑ j, (|(interNum (pp j) (fun _ : Fin (e j) => Nb.toSubSystem) : ℝ)| + |C j|) *
          (1 + (c' j : ℝ)) ^ (e j)) * ((n : ℝ) ^ d / n) := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_div]
    _ = _ := by rw [hkeyR]; ring

end GroundTheory.Heights₂.Heights.Kleiman
