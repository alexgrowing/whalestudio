import Formalism.SharpRestriction.GrowthBounds.RootWeights.LaurentDegreesSubstitutionSubset

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def binomialFunctions : AddSubgroup (ℤ → ℤ) := AddSubgroup.closure (Set.range fun k : ℕ => fun w : ℤ => Ring.choose w k)

theorem binomialFunctions_shift_mem (s : ℤ) (k : ℕ) : (fun w : ℤ => Ring.choose (w + s) k) ∈ binomialFunctions := by
  have h : (fun w : ℤ => Ring.choose (w + s) k) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, Ring.choose s ij.2 • (fun w : ℤ => Ring.choose w ij.1) := by
    funext w
    rw [Ring.add_choose_eq (h := Commute.all w s), Finset.sum_apply]
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp [mul_comm]
  rw [h]
  exact AddSubgroup.sum_mem _ fun ij _ =>
    AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self ij.1)) _

private theorem ring_choose_eq_zero_of_nonneg_of_lt (x : ℤ) (k : ℕ) (h0 : 0 ≤ x) (hk : x < k) : Ring.choose x k = 0 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  simp

private theorem ring_choose_self_of_eq (x : ℤ) (k : ℕ) (h : x = k) : Ring.choose x k = 1 := by
  subst h
  rw [Ring.choose_natCast, Nat.choose_self]
  simp

private theorem ring_choose_neg_one (k : ℕ) : Ring.choose (-1 : ℤ) k = (-1) ^ k := by
  induction k with
  | zero => simp [Ring.choose_zero_right]
  | succ k ih =>
    have h := Ring.choose_succ_succ (-1 : ℤ) k
    rw [neg_add_cancel, Ring.choose_zero_succ, ih] at h
    rw [pow_succ]
    linarith

theorem binomialFunctions_window_indicator (w0 : ℤ) (B : ℕ) : ∃ f ∈ binomialFunctions, ∀ w : ℤ, -(B : ℤ) ≤ w → w ≤ B →
    f w = if w = w0 then 1 else 0 := by
  induction B with
  | zero =>
    refine ⟨(if (0 : ℤ) = w0 then 1 else 0) • (fun w : ℤ => Ring.choose w 0),
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self 0)) _, ?_⟩
    intro w h1 h2
    have hw : w = 0 := by omega
    subst hw
    simp [Ring.choose_zero_right]
  | succ B ih =>
    obtain ⟨f, hf, hfw⟩ := ih
    have hg1 : (fun w : ℤ => Ring.choose (w + B) (2 * B + 1)) ∈ binomialFunctions := binomialFunctions_shift_mem _ _
    have hg2 : (fun w : ℤ => Ring.choose (w + ((B : ℤ) + 1)) (2 * B + 2)) ∈ binomialFunctions := binomialFunctions_shift_mem _ _
    set g1 : ℤ → ℤ := fun w : ℤ => Ring.choose (w + B) (2 * B + 1) with hg1d
    set g2 : ℤ → ℤ := fun w : ℤ => Ring.choose (w + ((B : ℤ) + 1)) (2 * B + 2) with hg2d
    set c1 : ℤ := (if (B : ℤ) + 1 = w0 then 1 else 0) - f ((B : ℤ) + 1) with hc1
    set c2 : ℤ := (if -((B : ℤ) + 1) = w0 then 1 else 0) - f (-((B : ℤ) + 1)) with hc2
    refine ⟨f + c1 • g2 + c2 • (g2 - g1),
      add_mem (add_mem hf (AddSubgroup.zsmul_mem _ hg2 _)) (AddSubgroup.zsmul_mem _ (sub_mem hg2 hg1) _), ?_⟩
    intro w h1 h2
    push_cast at h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases (by omega : (-(B : ℤ) ≤ w ∧ w ≤ B) ∨ w = B + 1 ∨ w = -((B : ℤ) + 1)) with h | h | h
    · have e1 : g1 w = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      have e2 : g2 w = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      rw [e1, e2, hfw w h.1 h.2]
      ring
    · subst h
      have e1 : g1 ((B : ℤ) + 1) = 1 := ring_choose_self_of_eq _ _ (by push_cast; ring)
      have e2 : g2 ((B : ℤ) + 1) = 1 := ring_choose_self_of_eq _ _ (by push_cast; ring)
      rw [e1, e2, hc1]
      ring
    · subst h
      have e1 : g1 (-((B : ℤ) + 1)) = -1 := by
        simp only [hg1d]
        rw [show -((B : ℤ) + 1) + B = -1 by ring, ring_choose_neg_one, pow_succ, pow_mul]
        simp
      have e2 : g2 (-((B : ℤ) + 1)) = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      rw [e1, e2, hc2]
      ring

section graded

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)

def diagonalMultiplier (a : Fin n) (f : ℤ → ℤ) (x : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ x.support, monomial m (x.coeff m * ((f (wtS LL S m a) : ℤ) : R))

open Classical in

def monomialRestriction (q : (ι × Fin n →₀ ℕ) → Prop) (x : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ x.support.filter q, monomial m (x.coeff m)

theorem coeff_diagonalMultiplier (a : Fin n) (f : ℤ → ℤ) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (diagonalMultiplier LL S a f x) = x.coeff m * ((f (wtS LL S m a) : ℤ) : R) := by
  classical
  simp only [diagonalMultiplier, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul]

open Classical in
theorem coeff_monomialRestriction (q : (ι × Fin n →₀ ℕ) → Prop) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (monomialRestriction q x) = if q m then x.coeff m else 0 := by
  simp only [monomialRestriction, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases hq : q m <;> by_cases hm : x.coeff m = 0 <;> simp [hq, hm]

theorem diagonalMultiplier_mem (W : Submodule R (MvPolynomial (ι × Fin n) R))
    (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) (a : Fin n) (f : ℤ → ℤ) (hf : f ∈ binomialFunctions) :
    ∀ x ∈ W, diagonalMultiplier LL S a f x ∈ W := by
  have hb : ∀ (k : ℕ) (x : MvPolynomial (ι × Fin n) R),
      binomPol R LL S a k x = diagonalMultiplier LL S a (fun w => Ring.choose w k) x := by
    intro k x
    conv_lhs => rw [x.as_sum]
    rw [map_sum]
    simp only [binomialOperator_monomial]
    rfl
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    intro x hx
    rw [← hb]
    exact hW a k x hx
  | zero =>
    intro x _
    have e : diagonalMultiplier LL S a 0 x = 0 := by
      ext m
      simp [coeff_diagonalMultiplier]
    rw [e]
    exact W.zero_mem
  | add f g _ _ hf hg =>
    intro x hx
    have e : diagonalMultiplier LL S a (f + g) x = diagonalMultiplier LL S a f x + diagonalMultiplier LL S a g x := by
      ext m
      simp [coeff_diagonalMultiplier, mul_add]
    rw [e]
    exact W.add_mem (hf x hx) (hg x hx)
  | neg f _ hf =>
    intro x hx
    have e : diagonalMultiplier LL S a (-f) x = -diagonalMultiplier LL S a f x := by
      ext m
      simp [coeff_diagonalMultiplier]
    rw [e]
    exact W.neg_mem (hf x hx)

theorem weightEntry_restriction_mem (W : Submodule R (MvPolynomial (ι × Fin n) R))
    (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) (a : Fin n) (w0 : ℤ) :
    ∀ x ∈ W, monomialRestriction (fun m => wtS LL S m a = w0) x ∈ W := by
  intro x hx
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ m ∈ x.support, -(B : ℤ) ≤ wtS LL S m a ∧ wtS LL S m a ≤ B := by
    refine ⟨∑ m ∈ x.support, (wtS LL S m a).natAbs, fun m hm => ?_⟩
    have h := Finset.single_le_sum (f := fun m => (wtS LL S m a).natAbs) (fun _ _ => Nat.zero_le _) hm
    have h2 : |wtS LL S m a| ≤ ((∑ m ∈ x.support, (wtS LL S m a).natAbs : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h
    exact ⟨by linarith [neg_abs_le (wtS LL S m a)], by linarith [le_abs_self (wtS LL S m a)]⟩
  obtain ⟨f, hf, hfw⟩ := binomialFunctions_window_indicator w0 B
  have e : monomialRestriction (fun m => wtS LL S m a = w0) x = diagonalMultiplier LL S a f x := by
    ext m
    rw [coeff_monomialRestriction, coeff_diagonalMultiplier]
    by_cases hm : m ∈ x.support
    · rw [hfw _ (hB m hm).1 (hB m hm).2]
      split_ifs <;> simp
    · rw [MvPolynomial.mem_support_iff, not_not] at hm
      simp [hm]
  rw [e]
  exact diagonalMultiplier_mem LL S W hW a f hf x hx

end graded

theorem binomial_stable_contains_components : BinomialStableContainsComponents := by
  intro R _ ι _ LL n S W hW x hx nu
  classical
  have key : ∀ s : Finset (Fin n), monomialRestriction (fun m => ∀ a ∈ s, wtS LL S m a = nu a) x ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : monomialRestriction (fun m => ∀ a ∈ (∅ : Finset (Fin n)), wtS LL S m a = nu a) x = x := by
        ext m
        rw [coeff_monomialRestriction]
        simp
      rw [e]
      exact hx
    | @insert a s _ ih =>
      have e : monomialRestriction (fun m => ∀ b ∈ insert a s, wtS LL S m b = nu b) x =
          monomialRestriction (fun m => wtS LL S m a = nu a) (monomialRestriction (fun m => ∀ b ∈ s, wtS LL S m b = nu b) x) := by
        ext m
        rw [coeff_monomialRestriction, coeff_monomialRestriction, coeff_monomialRestriction]
        by_cases h1 : wtS LL S m a = nu a <;> by_cases h2 : ∀ b ∈ s, wtS LL S m b = nu b <;>
          simp [h1, h2, Finset.forall_mem_insert]
      rw [e]
      exact weightEntry_restriction_mem LL S W hW a (nu a) _ ih
  have e : weightComponent LL S nu x = monomialRestriction (fun m => ∀ a ∈ Finset.univ, wtS LL S m a = nu a) x := by
    ext m
    rw [coeff_weightComponent, coeff_monomialRestriction]
    by_cases h : wtS LL S m = nu
    · have h' : ∀ a ∈ (Finset.univ : Finset (Fin n)), wtS LL S m a = nu a := fun a _ => by rw [h]
      rw [if_pos h, if_pos h']
    · have h' : ¬ ∀ a ∈ (Finset.univ : Finset (Fin n)), wtS LL S m a = nu a :=
        fun h'' => h (funext fun a => h'' a (Finset.mem_univ a))
      rw [if_neg h, if_neg h']
  rw [e]
  exact key _

end Formalism.MainNotions.G.GLWeightTheory
