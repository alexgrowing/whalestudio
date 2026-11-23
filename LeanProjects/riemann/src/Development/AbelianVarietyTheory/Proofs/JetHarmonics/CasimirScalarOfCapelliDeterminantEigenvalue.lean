import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliCasimir
open Polynomial

noncomputable def rev {ι : Type} (s : Finset ι) (f : ι → ℂ) : ℂ[X] := ∏ l ∈ s, (1 + C (f l) * X)

theorem rev_coeff {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    (rev s f).coeff 0 = 1 ∧ (rev s f).coeff 1 = ∑ l ∈ s, f l ∧
      2 * (rev s f).coeff 2 = (∑ l ∈ s, f l) ^ 2 - ∑ l ∈ s, f l ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rev, coeff_one]
  | insert a s ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
    have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
    have : rev (insert a s) f = rev s f + C (f a) * (X * rev s f) := by
      simp only [rev, prod_insert ha]; ring
    rw [this, sum_insert ha, sum_insert ha]
    simp only [coeff_add, coeff_C_mul]
    refine ⟨?_, ?_, ?_⟩
    · simp [h0]
    · rw [c1, h0, h1]; ring
    · rw [c2, h1]
      linear_combination h2

theorem rev_eval {ι : Type} (s : Finset ι) (f : ι → ℂ) (t : ℂ) (ht : t ≠ 0) :
    (rev s f).eval t = t ^ s.card * ∏ l ∈ s, (t⁻¹ + f l) := by
  rw [rev, eval_prod, ← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  simp; field_simp

theorem scalar_core (n : ℕ) (hn : 2 ≤ n) (ρ μ a : Fin n → ℂ) (b : Fin n → Fin n → ℂ) (r : ℕ → ℂ)
    (e c : ℂ)
    (h : ∀ Y : ℂ, (∏ l, (Y + ρ l)) * e + ∑ i, (∏ l ∈ univ.erase i, (Y + ρ l)) * a i
      + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (∏ l ∈ (univ.erase i).erase j, (Y + ρ l)) * b i j
      + ∑ d ∈ range (n - 2), (Y + c) ^ d * r d = (∏ l, (Y + μ l)) * e) :
    (∑ l, ρ l) * e + ∑ i, a i = (∑ l, μ l) * e ∧
    ((∑ l, ρ l) ^ 2 - ∑ l, ρ l ^ 2) * e + 2 * ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i
      + 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), b i j
      = ((∑ l, μ l) ^ 2 - ∑ l, μ l ^ 2) * e := by
  have key : C e * rev univ ρ + X * ∑ i, C (a i) * rev (univ.erase i) ρ
      + X ^ 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (b i j) * rev ((univ.erase i).erase j) ρ
      + X ^ 3 * ∑ d ∈ range (n - 2), C (r d) * X ^ (n - 3 - d) * (1 + C c * X) ^ d
      = C e * rev univ μ := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0:ℂ)).infinite_compl
    intro t ht
    have ht : t ≠ 0 := ht
    simp only [Set.mem_setOf_eq, eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_finset_sum,
      eval_one, rev_eval _ _ _ ht, card_univ, Fintype.card_fin]
    have := congrArg (fun z => t ^ n * z) (h t⁻¹)
    simp only [mul_add, mul_sum] at this ⊢
    refine Eq.trans ?_ (this.trans (by ring))
    congr 1
    · congr 1
      · congr 1
        · ring
        · refine sum_congr rfl fun i _ => ?_
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
          obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
          have : t ^ n = t * t ^ (n - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [this]; ring
      · refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
        have hij : j ≠ i := (mem_filter.1 hj).2.ne'
        rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _),
          card_univ, Fintype.card_fin]
        have : t ^ n = t ^ 2 * t ^ (n - 1 - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
    · refine sum_congr rfl fun d hd => ?_
      have hd := mem_range.1 hd
      have h1 : t ^ n = t ^ 3 * t ^ (n - 3 - d) * t ^ d := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have h2 : (1 + c * t) = t * (t⁻¹ + c) := by field_simp
      rw [h1, h2, mul_pow]; ring
  have k1 := congrArg (fun p => p.coeff 1) key
  have k2 := congrArg (fun p => p.coeff 2) key
  simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul'] at k1 k2
  have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
  have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
  rw [c1] at k1
  rw [c2] at k2
  simp only [finset_sum_coeff, coeff_C_mul, (rev_coeff _ _).1, (rev_coeff _ _).2.1, le_refl, if_true,
    Nat.sub_self, mul_one] at k1 k2
  norm_num at k1 k2
  constructor
  · linear_combination k1
  · have p1 := (rev_coeff univ ρ).2.2
    have p2 := (rev_coeff univ μ).2.2
    have : ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i = ∑ i, a i * (∑ l, ρ l - ρ i) := by
      refine sum_congr rfl fun i _ => ?_
      rw [sum_erase_eq_sub (mem_univ _), mul_comm]
    rw [this]
    linear_combination 2 * k2 - e * p1 + e * p2

theorem sum_sq_split {A : Type} [AddCommGroup A] {n : ℕ} (F : Fin n → Fin n → A) :
    ∑ i, ∑ j, F i j = ∑ i, F i i + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (F i j + F j i) := by
  have h1 : ∀ i j, F i j = (if i = j then F i j else 0) + (if i < j then F i j else 0)
      + (if j < i then F i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => h1 i j]
  simp only [sum_add_distrib, sum_filter, sum_ite_eq, mem_univ, if_true]
  rw [add_assoc, sum_comm (f := fun i j => if j < i then F i j else 0)]

theorem sum_diff {A : Type} [AddCommGroup A] [Module ℂ A] {n : ℕ} (x : Fin n → A) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (x i - x j)
      = ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • x i := by
  simp only [sum_sub_distrib]
  have : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), x j
      = ∑ j, ∑ i ∈ univ.filter (fun i => i < j), x j := by
    simp only [sum_filter]; exact sum_comm
  rw [this, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_const, sum_const, filter_lt_eq_Ioi, filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
  congr 1
  have := i.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

theorem sq_sub_cas {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) :
    (∑ i, E i i) * (∑ i, E i i) - Formalism.REAL.Cas E
      = (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i := by
  rw [← sum_diff, Formalism.REAL.Cas, sum_mul_sum, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  rw [sum_sq_split]
  simp only [sub_self, sum_const_zero, zero_add, smul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (mem_filter.1 hj).2.ne
  have h1 := hE i j j i
  have h2 := hE i i j j
  simp only [if_true, hij, hij.symm, if_false, sub_zero] at h1 h2
  rw [two_smul, ← h1, ← sub_eq_zero.1 h2]
  abel

theorem cas_of_capelli : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ), 2 ≤ n → Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → ∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w := by
  intro M _ _ n E mu hn hE h
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders (Module.End ℂ M) n E
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun φ : Module.Dual ℂ (Module.End ℂ M) =>
    scalar_core n hn ρ (fun s => (mu s : ℂ)) (fun i => φ (E i i))
      (fun i j => φ (E i i * E j j - E j i * E i j)) (fun d => φ (Rm d)) (φ 1) (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)
            = (∏ s, (Y + (mu s : ℂ))) • (1 : Module.End ℂ M) := by
          ext w; simpa using h Y w
        have h2 := congrArg φ ((hR _).symm.trans h1)
        simp only [map_add, map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h2
        exact h2)
  have e1 : ∑ i, E i i = (∑ l, (mu l : ℂ)) • (1 : Module.End ℂ M) := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := (core φ).1
    rw [hρ0] at this
    simp only [map_sub, map_sum, map_smul, smul_eq_mul]
    linear_combination this
  have e2 : Formalism.REAL.Cas E = (casG mu : ℂ) • (1 : Module.End ℂ M) := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have h2 := (core φ).2
    have h3 := congrArg φ (sq_sub_cas E hE)
    rw [e1, smul_mul_smul_comm, mul_one] at h3
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2
    simp only [map_sub φ, map_sum, map_smul, smul_eq_mul] at h3 h2 ⊢
    have h4 : (casG mu : ℂ) = ∑ l, (mu l : ℂ) ^ 2 - ∑ l, ρ l ^ 2 := by
      simp [casG, Formalism.QuantumDeterminants.rhoStd, hρ]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * φ (E i i)
        = - (2 * ∑ i, (0 - ρ i) * φ (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h4]
    rw [h5] at h3
    linear_combination -h3 - h2
  intro w
  rw [e2]; simp

end GlobalTheory.CapelliCasimir
