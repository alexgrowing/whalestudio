import Formalism.SubspaceCounting.StatementB

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.G0

namespace TailConcavityP

def g (k : ℕ) (b : ℝ) : ℝ := ∑ i ∈ range k, 1 / (b + i + 1)

lemma choose_cast (y k : ℕ) :
    ((y + k).choose k : ℝ) = ∏ i ∈ range k, (((y : ℝ) + i + 1) / (i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← ih]
    have h := Nat.add_one_mul_choose_eq (y + k) k
    have h2 : y + (k + 1) = y + k + 1 := by omega
    rw [h2]
    have h3 : (((y + k + 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
        ((y : ℝ) + k + 1) * (((y + k).choose k : ℕ) : ℝ) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h.symm
      push_cast at this
      linarith
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [mul_div_assoc', eq_div_iff hk]
    linarith

lemma fTail_eq (k y : ℕ) :
    fTail k y = ∑ i ∈ range k, (Real.log ((y : ℝ) + i + 1) - Real.log ((i : ℝ) + 1)) := by
  unfold fTail
  rw [choose_cast, Real.log_prod]
  · apply sum_congr rfl
    intro i _
    rw [Real.log_div] <;> positivity
  · intro i _
    positivity

lemma term_le (a b i : ℕ) :
    Real.log ((a : ℝ) + i + 1) - Real.log ((b : ℝ) + i + 1) ≤
      1 / ((b : ℝ) + i + 1) * ((a : ℝ) - b) := by
  have hb : (0 : ℝ) < b + i + 1 := by positivity
  have ha : (0 : ℝ) < a + i + 1 := by positivity
  rw [← Real.log_div ha.ne' hb.ne']
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have e : ((a : ℝ) + i + 1) / (b + i + 1) - 1 = 1 / ((b : ℝ) + i + 1) * ((a : ℝ) - b) := by
    field_simp
    ring
  linarith

lemma fTail_sub_le (k a b : ℕ) : fTail k a - fTail k b ≤ g k b * ((a : ℝ) - b) := by
  rw [fTail_eq, fTail_eq, ← sum_sub_distrib, g, sum_mul]
  apply sum_le_sum
  intro i _
  have := term_le a b i
  linarith

lemma g_nonneg (k : ℕ) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ g k b := by
  unfold g
  apply sum_nonneg
  intro i _
  positivity

lemma g_anti (k : ℕ) {b b' : ℝ} (hb : 0 ≤ b) (h : b ≤ b') : g k b' ≤ g k b := by
  unfold g
  apply sum_le_sum
  intro i _
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

lemma g_four {k : ℕ} {b : ℝ} (hb : (k : ℝ) ≤ b) : g k (4 * b) ≤ g k b / 2 := by
  unfold g
  rw [sum_div]
  apply sum_le_sum
  intro i hi
  have hi' : (i : ℝ) + 1 ≤ k := by
    have : i + 1 ≤ k := mem_range.mp hi
    exact_mod_cast this
  have hi0 : (0 : ℝ) ≤ i := i.cast_nonneg
  have h0 : (0 : ℝ) < b + i + 1 := by linarith
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

lemma g_lower {k : ℕ} {b : ℝ} (hk : (k : ℝ) ≤ b) (hb : 0 < b) : (k : ℝ) / (2 * b) ≤ g k b := by
  have h : ∑ i ∈ range k, (1 : ℝ) / (2 * b) ≤ g k b := by
    unfold g
    apply sum_le_sum
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ k := by
      have : i + 1 ≤ k := mem_range.mp hi
      exact_mod_cast this
    apply one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [sum_const, card_range, nsmul_eq_mul] at h
  calc (k : ℝ) / (2 * b) = k * (1 / (2 * b)) := by ring
    _ ≤ g k b := h

def cn (k N : ℕ) (B : Fin N → ℕ) (l : ℕ) : ℝ :=
  if h : l < N then g k (B ⟨l, h⟩) else 0

def en (k N : ℕ) (B : Fin N → ℕ) (u : ℕ) : ℝ :=
  cn k N B u - (if u = 0 then 0 else cn k N B (u - 1))

lemma tele (k N : ℕ) (B : Fin N → ℕ) (l : ℕ) :
    ∑ u ∈ range (l + 1), en k N B u = cn k N B l := by
  induction l with
  | zero => simp [en]
  | succ l ih =>
    rw [sum_range_succ, ih]
    simp [en]

end TailConcavityP

end Formalism.G0

open Formalism.G0.TailConcavityP in
theorem Formalism.G0.tail_concavity : TailConcavity := by
  intro N k' X u₀ α B hu hkB hB4 hT hX
  rcases Nat.eq_zero_or_pos k' with hk0 | hkpos
  · subst hk0
    simp [fTail]
  set U : Fin N := ⟨u₀, hu⟩ with hU
  have hbk : (k' : ℝ) ≤ B U := by exact_mod_cast hkB U
  have hkpos' : (0 : ℝ) < k' := by exact_mod_cast hkpos
  have hbpos : (0 : ℝ) < B U := lt_of_lt_of_le hkpos' hbk
  have hcn : ∀ l : Fin N, cn k' N B l.val = g k' (B l) := by
    intro l
    simp [cn, l.isLt]

  have hprev : ∀ u : Fin N, u.val ≠ 0 →
      ∃ hp : u.val - 1 < N, 4 * B u ≤ B ⟨u.val - 1, hp⟩ := by
    intro u hu0
    refine ⟨by omega, ?_⟩
    have h : (u.val - 1) + 1 < N := by omega
    have h4 := hB4 ⟨u.val - 1, by omega⟩ h
    have e : (⟨u.val - 1 + 1, h⟩ : Fin N) = u := Fin.ext (by dsimp; omega)
    rw [e] at h4
    exact h4
  have hen_eq : ∀ u : Fin N, u.val ≠ 0 → ∃ hp : u.val - 1 < N,
      en k' N B u.val = g k' (B u) - g k' (B ⟨u.val - 1, hp⟩) ∧ 4 * B u ≤ B ⟨u.val - 1, hp⟩ := by
    intro u hu0
    obtain ⟨hp, h4⟩ := hprev u hu0
    refine ⟨hp, ?_, h4⟩
    simp only [en, if_neg hu0, hcn u]
    simp [cn, hp]
  have hen0 : ∀ u : Fin N, u.val = 0 → en k' N B u.val = g k' (B u) := by
    intro u hu0
    simp only [en, hu0, if_true, sub_zero]
    rw [← hu0, hcn u]
  have en_nonneg : ∀ u : Fin N, 0 ≤ en k' N B u.val := by
    intro u
    by_cases hu0 : u.val = 0
    · rw [hen0 u hu0]
      exact g_nonneg k' (by positivity)
    · obtain ⟨hp, he, h4⟩ := hen_eq u hu0
      rw [he]
      have : ((B u : ℕ) : ℝ) ≤ (B ⟨u.val - 1, hp⟩ : ℝ) := by exact_mod_cast (by omega : B u ≤ B ⟨u.val - 1, hp⟩)
      have := g_anti k' (by positivity) this
      linarith

  let d : Fin N → ℝ := fun l => (α l : ℝ) - B l
  let D : Fin N → ℝ := fun u => ∑ l : Fin N, if u.val ≤ l.val then d l else 0
  have hD : ∀ u : Fin N, D u = (tailSum α u.val : ℝ) - tailSum B u.val := by
    intro u
    simp only [D, d, tailSum]
    push_cast
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro l _
    split_ifs <;> ring
  have D_nonpos : ∀ u : Fin N, D u ≤ 0 := by
    intro u
    rw [hD u]
    have : (tailSum α u.val : ℝ) ≤ tailSum B u.val := by exact_mod_cast hT u.val
    linarith
  have DU : D U ≤ -(X : ℝ) := by
    rw [hD U]
    have : (tailSum α u₀ : ℝ) + X ≤ tailSum B u₀ := by exact_mod_cast hX
    simp only [hU]
    linarith

  have step1 : ∑ l, fTail k' (α l) - ∑ l, fTail k' (B l) ≤ ∑ l, cn k' N B l.val * d l := by
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro l _
    rw [hcn l]
    exact fTail_sub_le k' (α l) (B l)

  have step2 : ∑ l, cn k' N B l.val * d l = ∑ u : Fin N, en k' N B u.val * D u := by
    have hc : ∀ l : Fin N, cn k' N B l.val =
        ∑ u : Fin N, if u.val ≤ l.val then en k' N B u.val else 0 := by
      intro l
      rw [Fin.sum_univ_eq_sum_range (fun u => if u ≤ l.val then en k' N B u else 0),
        ← sum_filter, ← tele]
      apply sum_congr _ (fun _ _ => rfl)
      ext u
      simp only [mem_filter, mem_range]
      have := l.isLt
      omega
    simp only [D, mul_sum]
    simp_rw [hc, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro l _
    split_ifs <;> simp

  have step3 : ∑ u : Fin N, en k' N B u.val * D u ≤ en k' N B U.val * D U := by
    rw [← Finset.add_sum_erase univ _ (mem_univ U)]
    have : ∑ x ∈ univ.erase U, en k' N B x.val * D x ≤ 0 :=
      sum_nonpos (fun x _ => mul_nonpos_of_nonneg_of_nonpos (en_nonneg x) (D_nonpos x))
    linarith

  have hgb := g_lower hbk hbpos
  have hen : (k' : ℝ) / (4 * B U) ≤ en k' N B U.val := by
    have e2 : (k' : ℝ) / (4 * B U) = (k' : ℝ) / (2 * B U) / 2 := by
      field_simp
      ring
    by_cases hu0 : U.val = 0
    · rw [hen0 U hu0, e2]
      have : (0 : ℝ) ≤ (k' : ℝ) / (2 * B U) := by positivity
      linarith
    · obtain ⟨hp, he, h4⟩ := hen_eq U hu0
      rw [he, e2]
      have h4' : 4 * ((B U : ℕ) : ℝ) ≤ (B ⟨U.val - 1, hp⟩ : ℝ) := by exact_mod_cast h4
      have h5 := g_anti k' (by positivity) h4'
      have h6 := g_four hbk
      linarith
  have step4 : en k' N B U.val * D U ≤ -((k' : ℝ) / (4 * B U) * X) := by
    have h1 : en k' N B U.val * D U ≤ en k' N B U.val * (-(X : ℝ)) :=
      mul_le_mul_of_nonneg_left DU (en_nonneg U)
    have h2 : (k' : ℝ) / (4 * B U) * X ≤ en k' N B U.val * X :=
      mul_le_mul_of_nonneg_right hen (by positivity)
    linarith
  have hfin : (X : ℝ) * k' / (4 * B U) = (k' : ℝ) / (4 * B U) * X := by ring
  show ∑ l, fTail k' (α l) ≤ ∑ l, fTail k' (B l) - (X : ℝ) * k' / (4 * B U)
  rw [hfin]
  linarith
