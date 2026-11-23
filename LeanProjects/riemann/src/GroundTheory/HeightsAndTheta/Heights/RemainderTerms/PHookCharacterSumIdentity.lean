import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Expand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

namespace HookSum

theorem card_filter_one_le_le (r m : ℕ) (hm : m < r) :
    (Finset.univ.filter fun j : Fin r => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m).card = m := by
  have h : (Finset.univ.filter fun j : Fin r => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m) =
      (Finset.Icc 1 m).attachFin (fun x hx => by rw [Finset.mem_Icc] at hx; omega) := by
    ext j
    simp [Finset.mem_attachFin]
  rw [h, Finset.card_attachFin, Nat.card_Icc]
  omega

theorem card_hookShape (r k l : ℕ) (hl : l < r) :
    (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ hookShape r k l i = 1).card = l := by
  have h : (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ hookShape r k l i = 1) =
      (Finset.univ.filter fun j : Fin r => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ l) := by
    apply Finset.filter_congr
    intro i _
    simp only [hookShape]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0]; omega
    · by_cases h1 : (i : ℕ) ≤ l
      · rw [if_neg h0, if_pos h1]; omega
      · rw [if_neg h0, if_neg h1]; omega
  rw [h, card_filter_one_le_le r l hl]

theorem sum_hookShape (r k l : ℕ) (hl : l < r) : ∑ i, hookShape r k l i = (k - l) + l := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  have h0 : hookShape (r' + 1) k l 0 = k - l := by simp [hookShape]
  have hs : ∀ i : Fin r', hookShape (r' + 1) k l i.succ = if (i : ℕ) < l then 1 else 0 := by
    intro i
    simp only [hookShape, Fin.val_succ]
    by_cases h : (i : ℕ) < l
    · rw [if_neg (by omega), if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg (by omega), if_neg h]
  rw [h0]
  simp only [hs]
  congr 1
  rw [Finset.sum_boole]
  have h : (Finset.univ.filter fun i : Fin r' => (i : ℕ) < l) =
      (Finset.range l).attachFin (fun x hx => by rw [Finset.mem_range] at hx; omega) := by
    ext j
    simp [Finset.mem_attachFin]
  rw [h, Finset.card_attachFin, Finset.card_range, Nat.cast_id]

theorem hookShape_mem (r k l : ℕ) (hlr : l < r) (hlk : l < k) :
    hookShape r k l ∈ partitionsOf r k := by
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨by rw [sum_hookShape r k l hlr]; omega, ?_⟩
  intro i j hij
  have := Fin.le_iff_val_le_val.mp hij
  simp only [hookShape]
  split_ifs <;> omega

theorem hookShape_isHook (r k l : ℕ) : ∀ i : Fin r, (i : ℕ) ≠ 0 → hookShape r k l i ≤ 1 := by
  intro i hi
  simp only [hookShape]
  split_ifs <;> omega

theorem hook_classification {r k : ℕ} (hk : 1 ≤ k) {nu : Fin r → ℕ}
    (hnu : nu ∈ partitionsOf r k) (hh : ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) {l : ℕ}
    (hl : (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card = l) :
    l < r ∧ l < k ∧ hookShape r k l = nu := by
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hnu
  obtain ⟨hsum, hA⟩ := hnu
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := by
    rcases r with _ | r'
    · simp at hsum; omega
    · exact ⟨r', rfl⟩
  set S := (Finset.univ.filter fun i : Fin (r' + 1) => (i : ℕ) ≠ 0 ∧ nu i = 1) with hSdef
  have down : ∀ i j : Fin (r' + 1), ((i : ℕ) ≠ 0 ∧ nu i = 1) → 1 ≤ (j : ℕ) → (j : ℕ) ≤ i →
      ((j : ℕ) ≠ 0 ∧ nu j = 1) := by
    intro i j hi hj1 hji
    have h1 := hA j i (Fin.le_iff_val_le_val.mpr hji)
    have h2 := hh j (by omega)
    exact ⟨by omega, by omega⟩
  have hiff : ∀ i : Fin (r' + 1), ((i : ℕ) ≠ 0 ∧ nu i = 1) ↔ (1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ l) := by
    intro i
    constructor
    · intro hP
      refine ⟨by omega, ?_⟩
      have hsub : (Finset.univ.filter fun j : Fin (r' + 1) => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ i) ⊆ S := by
        intro j hj
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact down i j hP hj.1 hj.2
      have := Finset.card_le_card hsub
      rw [card_filter_one_le_le (r' + 1) i i.isLt] at this
      omega
    · rintro ⟨h1, h2⟩
      by_contra hP
      have hsub : S ⊆ (Finset.univ.filter fun j : Fin (r' + 1) =>
          1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) - 1) := by
        intro j hj
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        refine ⟨by omega, ?_⟩
        by_contra hji
        exact hP (down j i hj (by omega) (by omega))
      have := Finset.card_le_card hsub
      rw [card_filter_one_le_le (r' + 1) ((i : ℕ) - 1) (by omega)] at this
      omega
  have hlr : l < r' + 1 := by
    have hsub : S ⊆ (Finset.univ.filter fun j : Fin (r' + 1) => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ r') := by
      intro j hj
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have := j.isLt
      omega
    have := Finset.card_le_card hsub
    rw [card_filter_one_le_le (r' + 1) r' (by omega)] at this
    omega
  have hval : ∀ i : Fin (r' + 1), (i : ℕ) ≠ 0 → nu i = if (i : ℕ) ≤ l then 1 else 0 := by
    intro i hi0
    have h := hiff i
    have h1 := hh i hi0
    split_ifs with hil
    · exact (h.mpr ⟨by omega, hil⟩).2
    · have : ¬ nu i = 1 := fun h' => by have := (h.mp ⟨hi0, h'⟩).2; omega
      omega
  have hsucc : ∀ i : Fin r', nu i.succ = hookShape (r' + 1) k l i.succ := by
    intro i
    rw [hval i.succ (by simp)]
    simp [hookShape]
  have hsumH := sum_hookShape (r' + 1) k l hlr
  rw [Fin.sum_univ_succ] at hsum hsumH
  have h0 : hookShape (r' + 1) k l 0 = k - l := by simp [hookShape]
  simp only [hsucc] at hsum
  rw [h0] at hsumH
  have hnu0 : nu 0 + l = k := by omega
  have hlk : l < k := by
    by_contra hlk
    have hnu00 : nu 0 = 0 := by omega
    have hl1 : 1 ≤ l := by omega
    obtain ⟨i1, hi1⟩ : ∃ i1 : Fin (r' + 1), (i1 : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
    have hP := (hiff i1).mpr ⟨by omega, by omega⟩
    have := hA 0 i1 (Fin.zero_le _)
    omega
  refine ⟨hlr, hlk, ?_⟩
  funext i
  by_cases hi : (i : ℕ) = 0
  · have : i = 0 := Fin.ext hi
    subst this
    rw [h0]
    omega
  · rw [hval i hi]
    simp [hookShape, hi]

theorem sum_hooks (r k : ℕ) (hk : 1 ≤ k) (g : (Fin r → ℕ) → ℚ) :
    ∑ nu ∈ partitionsOf r k, g nu *
        (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card)
        else 0) =
      ∑ l ∈ Finset.range (min r k), (-1 : ℚ) ^ l * g (hookShape r k l) := by
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun l => hookShape r k l)
    (fun nu => (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card)
  · intro l hl
    rw [Finset.mem_range, lt_min_iff] at hl
    rw [Finset.mem_filter]
    exact ⟨hookShape_mem r k l hl.1 hl.2, hookShape_isHook r k l⟩
  · intro nu hnu
    rw [Finset.mem_filter] at hnu
    obtain ⟨h1, h2, -⟩ := hook_classification hk hnu.1 hnu.2 rfl
    rw [Finset.mem_range, lt_min_iff]
    exact ⟨h1, h2⟩
  · intro l hl
    rw [Finset.mem_range, lt_min_iff] at hl
    exact card_hookShape r k l hl.1
  · intro nu hnu
    rw [Finset.mem_filter] at hnu
    exact (hook_classification hk hnu.1 hnu.2 rfl).2.2
  · intro l hl
    rw [Finset.mem_range, lt_min_iff] at hl
    rw [card_hookShape r k l hl.1, mul_comm]

end HookSum

theorem HookCharacterSumIdentity.proof (hSh : ShiftSumRule.Statement)
    (hL : LinearTermValue.Statement) (hF : SameFactorFormula.Statement)
    (hS : SchurSignCoefficient.Statement) (hR : RectangleTablePos.Statement)
    (hD : RestPolynomialDecomposes.Statement) : HookCharacterSumIdentity.Statement := by
  intro r a hr ha
  obtain ⟨Q, hQ⟩ := hD 1 r a .last
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hF 1 r a .last le_rfl hr ha
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hR r a).ne'
  have hJ' : fibreDegree 1 r a .last = C₀ * numStandardTable (rectangle r a) := by
    rw [hJ]
    have : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    rw [one_mul, pow_one, pow_one]
    field_simp
  have hterm : ∀ k ∈ Finset.Icc 2 (r + a),
      restTerm 1 (r + a) Q k 0 (smallPowerSum 1 r a .last (k - 1) 0) =
        C₀ * ∑ l ∈ Finset.range (min r k), (-1 : ℚ) ^ l *
          symmetricGroupCharacter (fun i => a + hookShape r k l i)
            ((k - 1) :: List.replicate (r * a + 1) 1) := by
    intro k hk
    obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
    obtain ⟨S, hS1, hS2⟩ := hT Q hQ k hk2 hkN 0
    have hex := fun nu (hnu : nu ∈ partitionsOf r k) =>
      hS (r + a) r k (by omega) hkN nu 1 (Or.inl rfl) (Top.antitone_of_mem_partitionsOf hnu)
        (Top.sum_of_mem_partitionsOf hnu)
    choose! Sν hSν1 hSν2 using hex
    have hSeq : S = ∑ nu ∈ partitionsOf r k,
        C (symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1)) *
          Sν nu := by
      apply Flag.powerSumHom_injective
      rw [hS1, map_sum]
      refine Finset.sum_congr rfl fun nu hnu => ?_
      rw [map_mul, hSν1 nu hnu]
      simp [powerSumHom, SmallBlock.sign]
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hcoeff : (k : ℚ) * coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1) S =
        ∑ nu ∈ partitionsOf r k,
          symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1) *
            (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
              (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card)
            else 0) := by
      rw [hSeq, coeff_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun nu hnu => ?_
      rw [coeff_C_mul, hSν2 nu hnu, one_pow, one_mul]
      split_ifs
      · field_simp
      · simp
    have hh := HookSum.sum_hooks r k (by omega)
      (fun nu => symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1))
    beta_reduce at hh
    rw [hS2, ← hh, ← hcoeff]
    have : ((r * a + 1).factorial : ℚ) ≠ 0 := by positivity
    simp only [one_mul, Nat.sub_self, pow_zero, mul_one]
    field_simp
  have hsh := hSh r a hr ha Q hQ
  have hlin := hL r a hr ha Q hQ
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hsh
  rw [hJ'] at hlin
  apply mul_left_cancel₀ (mul_ne_zero hC₀ hfR)
  linear_combination (-(a : ℚ)) * hlin + (numStandardTable (rectangle r a) : ℚ) * hsh

end

end RestTerms

end GroundTheory.Heights₂.Heights
