import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcMult

open Polynomial in

noncomputable def linProd {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) : k[X] :=
  ∏ i, (1 - Polynomial.C (a i) * Polynomial.X)

open Polynomial in
theorem linProd_ne_zero {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) :
    linProd a ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp [linProd, Polynomial.eval_prod] at this

open Polynomial in
theorem count_roots_factor {k : Type} [Field k] [DecidableEq k] (c y : k) (hy : y ≠ 0) :
    Multiset.count y⁻¹ (1 - Polynomial.C c * Polynomial.X).roots = if c = y then 1 else 0 := by
  by_cases hc : c = 0
  · subst hc
    have : (0 : k) ≠ y := fun h => hy h.symm
    simp [this]
  · have e : (1 - Polynomial.C c * Polynomial.X) = Polynomial.C (-c) * (Polynomial.X - Polynomial.C c⁻¹) := by
      rw [mul_sub, ← Polynomial.C_mul]
      simp [hc]
      ring
    rw [e, Polynomial.roots_C_mul _ (neg_ne_zero.mpr hc), Polynomial.roots_X_sub_C,
      Multiset.count_singleton]
    by_cases h : c = y
    · simp [h]
    · have : y⁻¹ ≠ c⁻¹ := fun h' => h (inv_injective h').symm
      simp [h, this]

open Polynomial in
theorem count_roots_linProd {k : Type} [Field k] [DecidableEq k] {ι : Type} [Fintype ι] (a : ι → k) (y : k)
    (hy : y ≠ 0) :
    Multiset.count y⁻¹ (linProd a).roots = (Finset.univ.filter fun i => a i = y).card := by
  classical
  have h := linProd_ne_zero a
  unfold linProd at h ⊢
  rw [Polynomial.roots_prod _ _ h, Multiset.count_bind]
  simp only [count_roots_factor _ _ hy]
  rw [Finset.card_filter]
  rfl

theorem coe_linProd {k : Type} [Field k] {ι : Type} [Fintype ι] (a : ι → k) :
    ((linProd a : Polynomial k) : PowerSeries k) = ∏ i, (1 - PowerSeries.C (a i) * PowerSeries.X) := by
  rw [linProd, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

end GlobalTheory.AlcMult

namespace GlobalTheory.AlcMult

theorem zmod_const_of_step (p : ℕ) [Fact p.Prime] (m m' : ZMod p → ℕ)
    (h : ∀ y : ZMod p, y + 1 ≠ 0 → m y + m' (y + 1) = m' y + m (y + 1))
    (hs : ∑ x, m x = ∑ x, m' x) : ∀ x, m x = m' x := by
  set d : ZMod p → ℤ := fun x => (m x : ℤ) - m' x with hd
  have step : ∀ y : ZMod p, y + 1 ≠ 0 → d (y + 1) = d y := by
    intro y hy
    have := h y hy
    simp only [hd]
    omega
  have hp := (Fact.out : p.Prime)
  have hn : ∀ n : ℕ, n < p → d (n : ZMod p) = d 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hlt
      have hne : ((n : ZMod p) + 1) ≠ 0 := by
        intro h0
        have : ((n + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact h0
        rw [ZMod.natCast_eq_zero_iff] at this
        exact absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)
      push_cast
      rw [step _ hne, ih (by omega)]
  have hc : ∀ x, d x = d 0 := by
    intro x
    have := hn x.val (ZMod.val_lt x)
    rwa [ZMod.natCast_zmod_val] at this
  have hsum : ∑ x, d x = 0 := by
    simp only [hd, Finset.sum_sub_distrib]
    have hs' : (∑ x, (m x : ℤ)) = ∑ x, (m' x : ℤ) := by exact_mod_cast hs
    rw [hs', sub_self]
  rw [Finset.sum_congr rfl (fun x _ => hc x), Finset.sum_const, Finset.card_univ, ZMod.card] at hsum
  have h0 : d 0 = 0 := by
    rcases smul_eq_zero.mp hsum with h | h
    · exact absurd h hp.ne_zero
    · exact h
  intro x
  have := hc x
  rw [h0] at this
  simp only [hd] at this
  omega

end GlobalTheory.AlcMult

namespace GlobalTheory.AlcMult

theorem card_cast_eq {p : ℕ} {k : Type} [Field k] [CharP k p] [DecidableEq k] {N : ℕ}
    (l : Fin N → ℕ) (z : ZMod p) :
    (Finset.univ.filter fun i => (l i : k) = ZMod.castHom (dvd_refl p) k z).card =
      (Finset.univ.filter fun i => (l i : ZMod p) = z).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← map_natCast (ZMod.castHom (dvd_refl p) k) (l i)]
  exact (ZMod.castHom_injective k).eq_iff

theorem card_cast_succ_eq {p : ℕ} {k : Type} [Field k] [CharP k p] [DecidableEq k] {N : ℕ}
    (l : Fin N → ℕ) (z : ZMod p) :
    (Finset.univ.filter fun i => (l i : k) + 1 = ZMod.castHom (dvd_refl p) k z).card =
      (Finset.univ.filter fun i => (l i : ZMod p) = z - 1).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← map_natCast (ZMod.castHom (dvd_refl p) k) (l i), ← map_one (ZMod.castHom (dvd_refl p) k),
    ← map_add, (ZMod.castHom_injective k).eq_iff, eq_sub_iff_add_eq]

theorem sum_card_fiber {p : ℕ} [NeZero p] {N : ℕ} (l : Fin N → ℕ) :
    ∑ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = N := by
  classical
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun i => (l i : ZMod p)) (s := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  simp

end GlobalTheory.AlcMult

open GlobalTheory.AlcMult in
theorem GlobalTheory.Alc.multiset_eq_of_series_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (l l' : Fin N → ℕ), (∏ i, (1 - PowerSeries.C ((l i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l' i : k) * PowerSeries.X) = (∏ i, (1 - PowerSeries.C ((l' i : k) + 1) * PowerSeries.X)) * ∏ i, (1 - PowerSeries.C (l i : k) * PowerSeries.X) → ∀ x : ZMod p, (Finset.univ.filter fun i => (l i : ZMod p) = x).card = (Finset.univ.filter fun i => (l' i : ZMod p) = x).card := by
  intro p hp k _ _ N l l' H
  haveI : Fact p.Prime := ⟨hp⟩
  letI : DecidableEq k := Classical.decEq k
  have HP : linProd (fun i => (l i : k) + 1) * linProd (fun i => (l' i : k)) =
      linProd (fun i => (l' i : k) + 1) * linProd (fun i => (l i : k)) := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_mul, Polynomial.coe_mul, coe_linProd, coe_linProd, coe_linProd, coe_linProd]
    exact H
  have hcount : ∀ y : k, y ≠ 0 →
      (Finset.univ.filter fun i => (l i : k) + 1 = y).card +
        (Finset.univ.filter fun i => (l' i : k) = y).card =
      (Finset.univ.filter fun i => (l' i : k) + 1 = y).card +
        (Finset.univ.filter fun i => (l i : k) = y).card := by
    intro y hy
    have e := congrArg (fun q => Multiset.count y⁻¹ q.roots) HP
    rw [Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)),
      Polynomial.roots_mul (mul_ne_zero (linProd_ne_zero _) (linProd_ne_zero _)),
      Multiset.count_add, Multiset.count_add, count_roots_linProd _ _ hy, count_roots_linProd _ _ hy,
      count_roots_linProd _ _ hy, count_roots_linProd _ _ hy] at e
    exact e
  apply zmod_const_of_step p
  · intro y hy
    have hne : ZMod.castHom (dvd_refl p) k (y + 1) ≠ 0 := by
      rw [← map_zero (ZMod.castHom (dvd_refl p) k)]
      exact fun h => hy ((ZMod.castHom_injective k) h)
    have := hcount _ hne
    rw [card_cast_succ_eq, card_cast_succ_eq, card_cast_eq, card_cast_eq, add_sub_cancel_right] at this
    exact this
  · rw [sum_card_fiber, sum_card_fiber]
