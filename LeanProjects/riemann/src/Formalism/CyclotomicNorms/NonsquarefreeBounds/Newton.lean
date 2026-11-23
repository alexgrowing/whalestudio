import Formalism.CyclotomicNorms.StatementA

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

namespace NewtonPolygonValuation

variable {L : Type} [Field L] (v : AddValuation L (WithTop ℝ))

lemma val_prod {ι : Type*} (s : Finset ι) (g : ι → L) :
    v (∏ i ∈ s, g i) = ∑ i ∈ s, v (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, AddValuation.map_mul, ih]

lemma val_root_eq_zero {z : L} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : v z = 0 := by
  have h := congrArg v hz
  rw [AddValuation.map_pow, AddValuation.map_one] at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact zero_ne_one hz
  have hne : v z ≠ ⊤ := (AddValuation.ne_top_iff v).2 hz0
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr] at h ⊢
  rw [← WithTop.coe_nsmul] at h
  have h1 : N • r = 0 := by exact_mod_cast h
  rw [nsmul_eq_mul] at h1
  have hr0 : r = 0 := by
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hN.ne')
    · exact h2
  rw [hr0]
  rfl

lemma val_sub_one_le {ζ : L} {N : ℕ} (hN : 0 < N) (hζ : ζ ^ N = 1) (i : ℕ) :
    v (ζ - 1) ≤ v (ζ ^ i - 1) := by
  rw [← geom_sum_mul, AddValuation.map_mul]
  have h0 : (0 : WithTop ℝ) ≤ v (∑ k ∈ range i, ζ ^ k) := by
    apply AddValuation.map_le_sum
    intro k _
    rw [AddValuation.map_pow, val_root_eq_zero v hN hζ, smul_zero]
  calc v (ζ - 1) = 0 + v (ζ - 1) := (zero_add _).symm
    _ ≤ _ := add_le_add h0 le_rfl

lemma val_zeta_sub_one {ℓ j : ℕ} (hℓ : ℓ.Prime) (hj : 1 ≤ j) (hv : v (ℓ : L) = wt 1) {z : L}
    (hz : IsPrimitiveRoot z (ℓ ^ j)) :
    v (z - 1) = wt (1 / ((ℓ ^ j).totient : ℝ)) := by
  classical
  have := Fact.mk hℓ
  have hpos : 0 < ℓ ^ j := pow_pos hℓ.pos j
  have : NeZero (ℓ ^ j) := ⟨hpos.ne'⟩
  have heq : ∀ μ ∈ primitiveRoots (ℓ ^ j) L, v (1 - μ) = v (z - 1) := by
    intro μ hμ
    rw [mem_primitiveRoots hpos] at hμ
    rw [AddValuation.map_sub_swap]
    apply le_antisymm
    · obtain ⟨i, -, hi⟩ := hμ.eq_pow_of_pow_eq_one hz.pow_eq_one
      rw [← hi]
      exact val_sub_one_le v hpos hμ.pow_eq_one i
    · obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hμ.pow_eq_one
      rw [← hi]
      exact val_sub_one_le v hpos hz.pow_eq_one i
  have hcyc := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hz)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [eval_one_cyclotomic_prime_pow, eval_prod] at hcyc
  simp only [eval_sub, eval_X, eval_C] at hcyc
  have h2 := congrArg v hcyc
  rw [hv, val_prod, sum_congr rfl heq, sum_const, hz.card_primitiveRoots] at h2
  have hne1 : z ≠ 1 := hz.ne_one (Nat.one_lt_pow (by omega) hℓ.one_lt)
  have hne : v (z - 1) ≠ ⊤ := (AddValuation.ne_top_iff v).2 (sub_ne_zero.2 hne1)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr] at h2 ⊢
  rw [← WithTop.coe_nsmul] at h2
  have h3 : (1 : ℝ) = ((ℓ ^ (k + 1)).totient : ℝ) * r := by
    have := WithTop.coe_injective h2
    rw [nsmul_eq_mul] at this
    exact this
  have hφ : (0 : ℝ) < ((ℓ ^ (k + 1)).totient : ℝ) := by exact_mod_cast Nat.totient_pos.2 hpos
  congr 1
  field_simp
  linarith

lemma val_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → L} {i₀ : ι}
    (hi : i₀ ∈ s) (h0 : v (g i₀) ≠ ⊤) (hlt : ∀ i ∈ s.erase i₀, v (g i₀) < v (g i)) :
    v (∑ i ∈ s, g i) = v (g i₀) := by
  rw [← add_sum_erase s g hi]
  exact AddValuation.map_add_eq_of_lt_left v (AddValuation.map_lt_sum v h0 hlt)

lemma wt_lt_add {a : WithTop ℝ} {x y : ℝ} (h : ∀ r : ℝ, a = r → x < r + y) :
    (x : WithTop ℝ) < a + y := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe r =>
    rw [← WithTop.coe_add]
    exact WithTop.coe_lt_coe.2 (h r rfl)

lemma val_term {x : L} {s : ℝ} (hx : v x = wt s) (a : L) (i : ℕ) :
    v (a * x ^ i) = v a + wt (i * s) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, hx, ← WithTop.coe_nsmul, nsmul_eq_mul]

end NewtonPolygonValuation

open NewtonPolygonValuation

theorem evaluation_bound : Evaluation := by
  intro L _ v ℓ e w j F z hℓ he hv hcoef hunit hz hφw
  classical
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hz
    subst hz
    have hw : w = 0 := by
      rw [pow_zero, Nat.totient_one, Nat.cast_one] at hφw
      have : e * w < 1 := by exact_mod_cast hφw
      rcases Nat.eq_zero_or_pos w with h | h
      · exact h
      · exact absurd this (by have := Nat.mul_le_mul he h; omega)
    subst hw
    obtain ⟨i, hi, hvi⟩ := hunit
    obtain rfl : i = 0 := by omega
    rw [sub_self, ← coeff_zero_eq_eval_zero, hvi]
    simp
  · set φ : ℝ := ((ℓ ^ j).totient : ℝ) with hφdef
    have hφpos : (0 : ℝ) < φ := by
      rw [hφdef]; exact_mod_cast Nat.totient_pos.2 (pow_pos hℓ.pos j)
    have hepos : (0 : ℝ) < e := by exact_mod_cast he
    set t : ℝ := 1 / φ with htdef
    have htpos : 0 < t := by positivity
    have hx : v (z - 1) = wt t := val_zeta_sub_one v hℓ hj hv hz
    have hex : ∃ i, i ≤ w ∧ v (F.coeff i) = wt 0 := by
      obtain ⟨i, hi, h⟩ := hunit; exact ⟨i, hi, h⟩
    set i₀ := Nat.find hex with hi₀def
    have hi₀w : i₀ ≤ w := (Nat.find_spec hex).1
    have hi₀v : v (F.coeff i₀) = wt 0 := (Nat.find_spec hex).2
    have hlow : ∀ i < i₀, wt (1 / e) ≤ v (F.coeff i) := by
      intro i hi
      have hn := Nat.find_min hex hi
      rcases hcoef i with h | h
      · exact absurd ⟨by omega, h⟩ hn
      · exact h
    have hnn : ∀ i, (0 : WithTop ℝ) ≤ v (F.coeff i) := by
      intro i
      rcases hcoef i with h | h
      · rw [h]; rfl
      · refine le_trans ?_ h
        exact WithTop.coe_le_coe.2 (by positivity)
    have hwt : (w : ℝ) * t < 1 / e := by
      have h1 : ((e * w : ℕ) : ℝ) < φ := hφw
      push_cast at h1
      rw [htdef, lt_div_iff₀ hepos]
      rw [mul_one_div, div_mul_eq_mul_div, div_lt_one hφpos]
      linarith
    have hne0 : F.coeff i₀ ≠ 0 := by
      rw [← AddValuation.ne_top_iff v, hi₀v]; exact WithTop.coe_ne_top
    have hmem : i₀ ∈ range (F.natDegree + 1) :=
      mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hne0))
    rw [eval_eq_sum_range]
    rw [val_sum_eq_of_lt v hmem ?_ ?_]
    · rw [val_term v hx, hi₀v, ← WithTop.coe_add, zero_add]
      apply WithTop.coe_le_coe.2
      rw [htdef, mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hi₀w) hφpos.le
    · rw [val_term v hx, hi₀v, ← WithTop.coe_add]; exact WithTop.coe_ne_top
    · intro i hi
      have hii : i ≠ i₀ := (mem_erase.1 hi).1
      rw [val_term v hx, val_term v hx, hi₀v, ← WithTop.coe_add, zero_add]
      apply wt_lt_add
      intro r hr
      rcases lt_or_gt_of_ne hii with h | h
      · have h1 := hlow i h
        rw [hr] at h1
        have h1' : 1 / (e : ℝ) ≤ r := WithTop.coe_le_coe.1 h1
        have : (i₀ : ℝ) * t ≤ w * t :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi₀w) htpos.le
        have : (0 : ℝ) ≤ i * t := by positivity
        linarith
      · have h1 := hnn i
        rw [hr] at h1
        have h1' : (0 : ℝ) ≤ r := WithTop.coe_le_coe.1 h1
        have : (i₀ : ℝ) * t < i * t :=
          mul_lt_mul_of_pos_right (by exact_mod_cast h) htpos
        linarith

end Formalism.CyclotomicNorms
