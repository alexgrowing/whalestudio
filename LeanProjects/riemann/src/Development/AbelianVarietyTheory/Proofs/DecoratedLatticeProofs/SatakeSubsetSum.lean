import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem two_mul_card_lt_pairs {N : ℕ} (S : Finset (Fin N)) :
    2 * ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card + S.card = S.card * S.card := by
  have hsw : ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card
      = ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _ r _ h
      exact Prod.swap_injective h
    · intro r hr
      refine ⟨r.swap, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hr ⊢
      exact ⟨⟨hr.1.2, hr.1.1⟩, hr.2⟩
  have hoff : S.offDiag = ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2) ∪
      ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_gt_of_ne h3 with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨⟨h1, h2⟩, h⟩)
      · exact ⟨h1, h2, ne_of_lt h⟩
      · exact ⟨h1, h2, ne_of_gt h⟩
  have hdisj : Disjoint ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2)
      ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hc := Finset.offDiag_card S
  rw [hoff, Finset.card_union_of_disjoint hdisj, ← hsw] at hc
  have hle : S.card ≤ S.card * S.card := Nat.le_mul_self _
  omega

theorem count_identity {N : ℕ} (S : Finset (Fin N)) :
    2 * ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card + 2 * ∑ a ∈ S, (a : ℕ)
      + S.card * (S.card + 1) = 2 * S.card * N := by
  classical
  have hP := two_mul_card_lt_pairs S
  have hsplit : ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card
      + ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card
      = ∑ a ∈ S, (Finset.Ioi a).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_add_sum_compl, ← Finset.card_filter, Finset.filter_lt_eq_Ioi]
  have hterm : ∀ a : Fin N, (Finset.Ioi a).card + (a : ℕ) + 1 = N := by
    intro a
    rw [Fin.card_Ioi]
    have := a.isLt
    omega
  have hsum : ∑ a ∈ S, (Finset.Ioi a).card + ∑ a ∈ S, (a : ℕ) + S.card = S.card * N := by
    have h0 : ∑ a ∈ S, ((Finset.Ioi a).card + (a : ℕ) + 1) = S.card * N := by
      rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_const, smul_eq_mul]
    rwa [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h0
  nlinarith [hP, hsplit, hsum]

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem prod_zpow_eq {ι : Type} (s : ℂ) (hs : s ≠ 0) (S : Finset ι) (e : ι → ℤ) :
    ∏ a ∈ S, s ^ e a = s ^ (∑ a ∈ S, e a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert b T hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add₀ hs]

theorem cpow_half_int (q : ℕ) (m : ℤ) :
    (q : ℂ) ^ ((m : ℂ) / 2) = ((Real.sqrt q : ℝ) : ℂ) ^ m := by
  have h1 : ((q : ℝ) : ℂ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) = ((((q : ℝ) ^ ((m : ℝ) / 2) : ℝ)) : ℂ) :=
    (Complex.ofReal_cpow (Nat.cast_nonneg q) _).symm
  have h2 : (q : ℝ) ^ ((m : ℝ) / 2) = (Real.sqrt q) ^ m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  rw [h2] at h1
  push_cast at h1
  exact h1

theorem borelParam_eq (q N : ℕ) (α : Fin N → ℂˣ) (a : Fin N) :
    borelParam q α a = (α a : ℂ) * ((Real.sqrt q : ℝ) : ℂ) ^ (2 * (a : ℤ) - N + 1) := by
  unfold borelParam
  rw [← cpow_half_int]
  congr 2
  push_cast
  ring

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem term_eq (q N : ℕ) (hq : 0 < q) (α : Fin N → ℂˣ) (S : Finset (Fin N)) :
    (q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a
      = ((Real.sqrt q : ℝ) : ℂ) ^ (S.card * (N - S.card)) * ∏ a ∈ S, (α a : ℂ) := by
  set s : ℂ := ((Real.sqrt q : ℝ) : ℂ) with hsdef
  have hs : s ≠ 0 := by
    rw [hsdef, Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast hq
  have hs2 : (q : ℂ) = s ^ 2 := by
    rw [hsdef, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  have hnN : S.card ≤ N := by
    simpa using Finset.card_le_univ S
  set inv := ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card with hinv
  have hcount := count_identity S
  rw [← hinv] at hcount
  simp_rw [borelParam_eq]
  rw [Finset.prod_mul_distrib, prod_zpow_eq s hs, hs2, ← pow_mul, ← zpow_natCast, ← zpow_natCast,
    mul_left_comm, ← zpow_add₀ hs, mul_comm]
  congr 2
  have hc : ((2 * inv + 2 * ∑ a ∈ S, (a : ℕ) + S.card * (S.card + 1) : ℕ) : ℤ) = ((2 * S.card * N : ℕ) : ℤ) := by
    rw [hcount]
  push_cast at hc
  push_cast [Nat.cast_sub hnN]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul]
  push_cast
  linear_combination hc

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem satake_subset_sum : ∀ (q N : ℕ), 0 < q → ∀ (α : Fin N → ℂˣ) (n : ℕ),
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      ((q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a)
      = genVal q 0 N (Finset.univ.val.map α) n := by
  intro q N hq α n
  unfold genVal
  rw [Multiset.map_map, Finset.esymm_map_val, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  rw [term_eq q N hq α S, hS.2, zero_mul, zero_add]
  rfl

end GlobalTheory.SatakeSubsetSum
