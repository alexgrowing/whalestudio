import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUpUniMul

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Matrix

section Bru

variable {K : Type} [Field K] {n : ℕ}

theorem bru_lo_one : IsLoUni (1 : Matrix (Fin n) (Fin n) K) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩

theorem bru_up_one : IsUpUni (1 : Matrix (Fin n) (Fin n) K) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩

theorem bru_lo_mul {A B : Matrix (Fin n) (Fin n) K} (hA : IsLoUni A) (hB : IsLoUni B) : IsLoUni (A * B) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : i < k
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_le_of_lt (not_lt.1 hk) hij), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hB k i).1 h, mul_zero]
      · rw [(hA i k).1 h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem bru_up_mul {A B : Matrix (Fin n) (Fin n) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  first | exact GlobalTheory.UpperUnipotentMul.isUpUni_mul .. | (apply GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentMul.isUpUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n A B hA hB | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n A B hA | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n A B | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n A | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› n | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K ‹_› | exact @GlobalTheory.UpperUnipotentMul.isUpUni_mul K

def bruL (u : Fin n → K) (p : Fin n) : Matrix (Fin n) (Fin n) K :=
  fun a k => (if a = k then 1 else 0) + u a * (if k = p then 1 else 0)

def bruU (w : Fin n → K) (q : Fin n) : Matrix (Fin n) (Fin n) K :=
  fun k c => (if k = c then 1 else 0) + (if k = q then 1 else 0) * w c

theorem bruL_apply (u : Fin n → K) (p a k : Fin n) :
    bruL u p a k = (if a = k then 1 else 0) + u a * (if k = p then 1 else 0) := rfl

theorem bruU_apply (w : Fin n → K) (q k c : Fin n) :
    bruU w q k c = (if k = c then 1 else 0) + (if k = q then 1 else 0) * w c := rfl

theorem bru_left (u : Fin n → K) (p : Fin n) (X : Matrix (Fin n) (Fin n) K) (a c : Fin n) :
    (bruL u p * X) a c = X a c + u a * X p c := by
  simp only [Matrix.mul_apply, bruL, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp
  · simp

theorem bru_right (w : Fin n → K) (q : Fin n) (X : Matrix (Fin n) (Fin n) K) (a c : Fin n) :
    (X * bruU w q) a c = X a c + X a q * w c := by
  simp only [Matrix.mul_apply, bruU, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp
  · simp

def bruRed (m : ℕ) (M : Matrix (Fin n) (Fin n) K) (σ : Fin n → Fin n) : Prop :=
  (∀ b b' : Fin n, b.val < m → b'.val < m → σ b = σ b' → b = b') ∧
  (∀ b : Fin n, b.val < m → M (σ b) b ≠ 0) ∧
  (∀ b : Fin n, b.val < m → ∀ a, a ≠ σ b → M a b = 0) ∧
  (∀ b : Fin n, b.val < m → ∀ c, c ≠ b → M (σ b) c = 0)

theorem bru_step {m : ℕ} (hm : m < n) (M : Matrix (Fin n) (Fin n) K) (hdet : M.det ≠ 0) (σ : Fin n → Fin n)
    (h : bruRed m M σ) :
    ∃ (L U M' : Matrix (Fin n) (Fin n) K) (σ' : Fin n → Fin n), IsLoUni L ∧ IsUpUni U ∧ M = L * M' * U ∧
      bruRed (m + 1) M' σ' := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨q, hq⟩ : ∃ q : Fin n, q.val = m := ⟨⟨m, hm⟩, rfl⟩
  have hne : ∃ a, M a q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero q hc)
  obtain ⟨p, hp, hmin⟩ : ∃ p, M p q ≠ 0 ∧ ∀ a, a < p → M a q = 0 := by
    have hs : (Finset.univ.filter (fun a => M a q ≠ 0)).Nonempty := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, by simp [ha]⟩
    refine ⟨(Finset.univ.filter (fun a => M a q ≠ 0)).min' hs, ?_, ?_⟩
    · have := Finset.min'_mem _ hs
      simpa using this
    · intro a ha
      by_contra hc
      have hmem : a ∈ Finset.univ.filter (fun a => M a q ≠ 0) := by simp [hc]
      exact absurd (Finset.min'_le _ a hmem) (not_le.2 ha)
  have hqb : ∀ b : Fin n, b.val < m → q ≠ b := by
    intro b hb e
    rw [← e, hq] at hb
    exact lt_irrefl _ hb
  have hpσ : ∀ b : Fin n, b.val < m → p ≠ σ b := by
    intro b hb e
    exact hp (e ▸ h4 b hb q (hqb b hb))
  have hrow : ∀ c : Fin n, c.val < m → M p c = 0 := fun c hc => h3 c hc p (hpσ c hc)
  have hcase : ∀ b : Fin n, b.val < m + 1 → b = q ∨ b.val < m := by
    intro b hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext (h.trans hq.symm))
  obtain ⟨u, hu⟩ : ∃ u : Fin n → K, ∀ a, u a = if a = p then 0 else M a q / M p q := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin n → K, ∀ c, w c = if c = q then 0 else M p c / M p q := ⟨_, fun _ => rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin n) (Fin n) K, ∀ a c, M' a c =
      if a = p then (if c = q then M p q else 0) else M a c - M a q / M p q * M p c :=
    ⟨Matrix.of fun a c => if a = p then (if c = q then M p q else 0) else M a c - M a q / M p q * M p c,
      fun _ _ => rfl⟩
  refine ⟨bruL u p, bruU w q, M', Function.update σ q p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [bruL_apply, if_neg (ne_of_lt hij), zero_add]
      by_cases hj : j = p
      · subst hj
        rw [hu, if_neg (ne_of_lt hij), hmin i hij, zero_div, zero_mul]
      · rw [if_neg hj, mul_zero]
    · subst hij
      rw [bruL_apply, if_pos rfl, hu]
      by_cases hi : i = p
      · rw [if_pos hi, zero_mul, add_zero]
      · rw [if_neg hi, if_neg hi, mul_zero, add_zero]
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [bruU_apply, if_neg (ne_of_gt hij), zero_add]
      by_cases hi : i = q
      · subst hi
        rw [hw, if_neg (ne_of_lt hij), hrow j (by rw [← hq]; exact hij), zero_div, mul_zero]
      · rw [if_neg hi, zero_mul]
    · subst hij
      rw [bruU_apply, if_pos rfl, hw]
      by_cases hi : i = q
      · rw [if_pos hi, if_pos hi, mul_zero, add_zero]
      · rw [if_neg hi, zero_mul, add_zero]
  · ext a c
    rw [bru_right, bru_left, bru_left, hu, hw, hM', hM', hM', hM']
    by_cases ha : a = p
    · subst ha
      by_cases hc : c = q
      · subst hc
        simp
      · simp only [if_true, if_neg hc]
        field_simp
        ring
    · by_cases hc : c = q
      · subst hc
        simp only [if_true, if_neg ha]
        field_simp
        ring
      · simp only [if_true, if_neg ha, if_neg hc]
        field_simp
        ring
  · intro b b' hb hb' e
    rcases hcase b hb with rfl | hb1
    · rcases hcase b' hb' with rfl | hb1'
      · rfl
      · rw [Function.update_self, Function.update_of_ne (hqb b' hb1').symm] at e
        exact absurd e (hpσ b' hb1')
    · rcases hcase b' hb' with rfl | hb1'
      · rw [Function.update_self, Function.update_of_ne (hqb b hb1).symm] at e
        exact absurd e.symm (hpσ b hb1)
      · rw [Function.update_of_ne (hqb b hb1).symm, Function.update_of_ne (hqb b' hb1').symm] at e
        exact h1 b b' hb1 hb1' e
  · intro b hb
    rcases hcase b hb with rfl | hb1
    · rw [Function.update_self, hM', if_pos rfl, if_pos rfl]
      exact hp
    · rw [Function.update_of_ne (hqb b hb1).symm, hM', if_neg (hpσ b hb1).symm,
        h4 b hb1 q (hqb b hb1), zero_div, zero_mul, sub_zero]
      exact h2 b hb1
  · intro b hb a ha
    rcases hcase b hb with rfl | hb1
    · rw [Function.update_self] at ha
      rw [hM', if_neg ha, div_mul_cancel₀ _ hp, sub_self]
    · rw [Function.update_of_ne (hqb b hb1).symm] at ha
      rw [hM']
      by_cases hap : a = p
      · rw [if_pos hap, if_neg (hqb b hb1).symm]
      · rw [if_neg hap, h3 b hb1 a ha, hrow b hb1, mul_zero, sub_zero]
  · intro b hb c hc
    rcases hcase b hb with rfl | hb1
    · rw [Function.update_self, hM', if_pos rfl, if_neg hc]
    · rw [Function.update_of_ne (hqb b hb1).symm, hM', if_neg (hpσ b hb1).symm,
        h4 b hb1 c hc, h4 b hb1 q (hqb b hb1), zero_div, zero_mul, sub_zero]

theorem bru_all (Z : Matrix (Fin n) (Fin n) K) (hdet : Z.det ≠ 0) : ∀ m : ℕ, m ≤ n →
    ∃ (L U M : Matrix (Fin n) (Fin n) K) (σ : Fin n → Fin n), IsLoUni L ∧ IsUpUni U ∧ Z = L * M * U ∧ bruRed m M σ := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨1, 1, Z, id, bru_lo_one, bru_up_one, by simp,
      fun b _ hb => absurd hb (Nat.not_lt_zero _), fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b hb => absurd hb (Nat.not_lt_zero _), fun b hb => absurd hb (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨L, U, M, σ, hL, hU, hZ, hR⟩ := ih (Nat.le_of_succ_le hm)
    have hM : M.det ≠ 0 := by
      intro h0
      apply hdet
      rw [hZ, Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]
    obtain ⟨L1, U1, M', σ', hL1, hU1, hM', hR'⟩ := bru_step (Nat.lt_of_succ_le hm) M hM σ hR
    refine ⟨L * L1, U1 * U, M', σ', bru_lo_mul hL hL1, bru_up_mul hU1 hU, ?_, hR'⟩
    rw [hZ, hM']
    simp only [Matrix.mul_assoc]

end Bru

theorem cell_bruhat : BruhatDecomposition := by
  intro K _ n Z hdet
  obtain ⟨L, U, M, σ, hL, hU, hZ, h1, h2, h3, _⟩ := bru_all Z hdet n le_rfl
  have hinj : Function.Injective σ := fun b b' e => h1 b b' b.isLt b'.isLt e
  refine ⟨L, U, σ, fun b => M (σ b) b, hL, hU, Finite.injective_iff_bijective.1 hinj, fun b => h2 b b.isLt, ?_⟩
  have hMm : M = mono σ (fun b => M (σ b) b) := by
    ext a b
    unfold mono
    by_cases hab : a = σ b
    · rw [if_pos hab, hab]
    · rw [if_neg hab, h3 b b.isLt a hab]
  rw [← hMm]
  exact hZ

end Formalism.MainNotions.BridgeLemma

end
