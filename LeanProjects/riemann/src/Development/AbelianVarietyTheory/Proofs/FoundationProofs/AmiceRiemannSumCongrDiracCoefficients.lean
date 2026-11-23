import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
import Development.AbelianVarietyTheory.Definitions.Foundations.MapEvalOfFixCoeff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp.RiemannDirac

variable {l : ℕ} [Fact l.Prime]

theorem norm_tval_sub_tval_le (F : PowerSeries (Qbar l)) (hF : ∀ n, ‖F.coeff n‖ ≤ 1) {z : Qbar l} (hz : ‖z - 1‖ ≤ 1)
    {M N : ℕ} (h : M ≤ N) : ‖tval F N z - tval F M z‖ ≤ ‖z - 1‖ ^ M := by
  unfold tval
  rw [← Finset.sum_Ico_eq_sub _ h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n hn => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (hF n)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hz (Finset.mem_Ico.1 hn).1)

theorem sum_root_pow {r : ℕ} {ξ : Qbar l} (hξ : IsPrimitiveRoot ξ (l ^ r)) {x : ℕ} (hx : x < l ^ r) (j : ℕ) :
    ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * (ξ ^ k) ^ j =
      if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0 := by
  have hpos : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  rw [← mass_dirac hξ hx (Nat.mod_lt j hpos)]
  unfold mass
  refine Finset.sum_congr rfl fun k _ => ?_
  have hy : j % l ^ r < l ^ (3 * r) :=
    (Nat.mod_lt j hpos).trans_le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (by omega))
  have h1 : (ξ ^ k) ^ (l ^ r) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  rw [tval_dirac hy, ← pow_eq_pow_mod j h1]

theorem norm_mass_sub_le {F : PowerSeries (Qbar l)} {a : ℕ → Qbar l} {N r : ℕ} {ξ : Qbar l} (hN : l ^ (3 * r) ≤ N)
    (hF : ∀ n, ‖F.coeff n‖ ≤ 1) (ht : ∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j)
    (hξ : IsPrimitiveRoot ξ (l ^ r)) {x : ℕ} (hx : x < l ^ r) :
    ‖mass F r ξ x - ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)‖ ≤
      ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  have hn : ‖ξ‖ = 1 := by
    have h1 := congrArg norm hξ.pow_eq_one
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h1
  have e : ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) =
      ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * tval F N (ξ ^ k) := by
    simp_rw [ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_root_pow hξ hx j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e, mass, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k _ => ?_
  have h1 : (ξ ^ k) ^ (l ^ r) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  rw [← mul_sub, norm_mul, norm_pow ξ, hn, one_pow, one_mul, norm_sub_rev]
  exact (norm_tval_sub_tval_le F hF (GlobalTheory.AmiceDist.norm_sub_one_le h1) hN).trans
    (GlobalTheory.AmiceDist.norm_sub_one_pow_three_le h1)

theorem norm_term_sub_le (φ : DirichletCharacter (Qbar l) l) (e : ℕ) {r : ℕ} (hr : 1 ≤ r) (j : ℕ) :
    ‖∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
        φ (x : ZMod l) * ((x : Qbar l) ^ e) * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) -
      (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  have hpos : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have hd : l ∣ l ^ r := dvd_pow_self l (by omega)
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · have hc : ((j % l ^ r : ℕ) : ZMod l) = (j : ZMod l) := by
      rw [← ZMod.natCast_mod (j % l ^ r) l, Nat.mod_mod_of_dvd _ hd, ZMod.natCast_mod]
    obtain ⟨c, hc'⟩ := ((Nat.mod_modEq j (l ^ r)).pow e).symm.dvd
    have h2 : ((j % l ^ r : ℕ) : Qbar l) ^ e - (j : Qbar l) ^ e = (l : Qbar l) ^ r * (c : Qbar l) := by
      have := congrArg (Int.cast : ℤ → Qbar l) hc'
      simpa only [Int.cast_sub, Int.cast_natCast, Nat.cast_pow, Int.cast_mul, Int.cast_pow] using this
    have h3 : φ ((j % l ^ r : ℕ) : ZMod l) * ((j % l ^ r : ℕ) : Qbar l) ^ e * (l : Qbar l) ^ r -
        (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e) =
        (l : Qbar l) ^ (2 * r) * (φ (j : ZMod l) * (c : Qbar l)) := by
      rw [hc]
      linear_combination (φ (j : ZMod l) * (l : Qbar l) ^ r) * h2
    rw [h3, norm_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (mul_le_one₀ (φ.norm_le_one _) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _))
  · have h1 : l ∣ j := by
      rw [Finset.mem_filter, Finset.mem_range] at h
      by_contra h0
      exact h ⟨Nat.mod_lt j hpos, fun h' => h0 ((Nat.dvd_mod_iff hd).1 h')⟩
    rw [(ZMod.natCast_eq_zero_iff j l).2 h1, MulChar.map_zero]
    simp only [zero_mul, mul_zero, sub_zero, norm_zero, norm_nonneg]

theorem rSum_cg : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l))
    (a : ℕ → Qbar l) (N r : ℕ) (ξ : Qbar l), 1 ≤ r → l ^ (3 * r) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ j, ‖a j‖ ≤ 1) →
    (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot ξ (l ^ r) →
    Cg (2 * r) (rSum φ e F r ξ)
      ((l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)) := by
  intro l _ φ e F a N r ξ hr hN hF ha ht hξ
  have h1 : ‖rSum φ e F r ξ - ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
      ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
    rw [rSum, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x hx => ?_
    rw [← mul_sub, norm_mul, norm_mul, norm_pow (x : Qbar l)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (φ.norm_le_one _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)))).trans
      (norm_mass_sub_le hN hF ht hξ (Finset.mem_range.1 (Finset.mem_filter.1 hx).1))
  have h2 : ‖(∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
      ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)) -
      (l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
    have e1 : (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
        (a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0))) -
        (l : Qbar l) ^ r * (a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)) =
        a j * (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) -
          (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e)) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun x _ => by ring
      · ring
    rw [e1, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha j)).trans (norm_term_sub_le φ e hr j)
  unfold Cg
  rw [← sub_add_sub_cancel]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

end GlobalTheory.KZ.Cmp.RiemannDirac
