import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
set_option maxSynthPendingDepth 1

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.LowMeet

variable {n : ℕ}

theorem not_hasUpper {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ¬ HasUpper m := by
  rintro ⟨a, ha, hne⟩
  exact not_lower_of_upper ha (hm a (Finsupp.mem_support_iff.2 hne))

theorem lowPart_eq {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : lowPart m = m := by
  ext a
  simp only [lowPart, Finsupp.filter_apply]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hm a (Finsupp.mem_support_iff.2 (Ne.symm hne)))

theorem diagExp_eq {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : diagExp m = 0 := by
  ext i
  rw [diagExp_apply]
  by_contra hne
  exact not_lower_of_diag (a := (i, i)) rfl (hm (i, i) (Finsupp.mem_support_iff.2 hne))

theorem recover (lam : Fin n → ℂ) {x : U n} (hx : x ∈ lowSpan n) :
    Finsupp.linearCombination ℂ (canon (n := n)) (vermaCoord lam x) = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [vermaCoord_canon_of_not lam (not_hasUpper hm), lowPart_eq hm, diagExp_eq hm]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r x _ hx => rw [map_smul, map_smul, hx]

theorem eq_zero_of_mem (lam : Fin n → ℂ) {x : U n} (hx : x ∈ lowSpan n)
    (hJ : x ∈ vermaIdeal lam) : x = 0 := by
  rw [← recover lam hx, vermaCoord_vermaIdeal lam hJ, map_zero]

theorem canonSpan_lower_le (lo hi : ℕ) : canonSpan (IsLower (n := n)) lo hi ≤ lowSpan n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact ⟨m, hm, rfl⟩

theorem word_mem_lowSpan {w : List (Fin n × Fin n)} (hw : ∀ a ∈ w, IsLower a) :
    word w ∈ lowSpan n :=
  canonSpan_lower_le _ _ (word_mem_canonSpan closed_lower w hw)

theorem isLower_simple {i j : Fin n} (hij : (j : ℕ) = i + 1) : IsLower (j, i) := by
  simp only [IsLower]; rw [Fin.lt_def, hij]; omega

theorem mul_sq_mem_lowSpan {a : Fin n × Fin n} (ha : IsLower a) {x : U n} (hx : x ∈ lowSpan n) :
    x * e a ^ 2 ∈ lowSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    have h : canon m * e a ^ 2 = word (expand m ++ [a, a]) := by
      rw [word_append, word_cons, word_singleton, pow_two]; rfl
    rw [h]
    refine word_mem_lowSpan fun b hb => ?_
    rcases List.mem_append.1 hb with hb | hb
    · exact hm b (mem_support_of_mem_expand hb)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
      rw [hb]; exact ha
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

def lowSq (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (v : U n) (i j : Fin n), v ∈ lowSpan n ∧ (j : ℕ) = i + 1 ∧
    v * e (j, i) ^ 2 = x}

theorem lowSq_le_lowSpan : lowSq n ≤ lowSpan n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, i, j, hv, hij, rfl⟩
  exact mul_sq_mem_lowSpan (isLower_simple hij) hv

theorem lowSq_le_sqSpan : lowSq n ≤ sqSpan n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨v, i, j, -, hij, rfl⟩
  exact ⟨v, i, j, hij, rfl⟩

theorem canon_mul_sq_mem (m : Fin n × Fin n →₀ ℕ) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    canon m * e (j, i) ^ 2 ∈ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  by_cases h : HasUpper m
  · refine Submodule.mem_sup_right ?_
    exact mul_pow_mem_vermaIdeal hij (rhoVec n) 1 (by rw [rhoVec_sub hij]; simp)
      (canon_mem_nPlusU h)
  · have hup : ∀ a ∈ upL n, m a = 0 := fun a ha => by
      by_contra hne; exact h ⟨a, mem_upL.1 ha, hne⟩
    set low := word (blockW (lowL n) m) with hlow
    have hlowS : low ∈ lowSpan n :=
      word_mem_lowSpan fun a ha => mem_lowL.1 (mem_of_mem_blockW ha).1
    set p := MvPolynomial.monomial (diagExp m) (1 : ℂ)
    set q := translate (fun k => ((2 : ℕ) : ℂ) * rootAt (j, i) k) p
    have hc : canon m * e (j, i) ^ 2 = low * e (j, i) ^ 2 * hcEmb q := by
      rw [canon_eq_triangular, blockW_eq_nil hup, word_nil, mul_one, mul_assoc,
        hcEmb_mul_e_pow, mul_assoc]
    have hs : canon m * e (j, i) ^ 2 =
        MvPolynomial.eval (rhoVec n) q • (low * e (j, i) ^ 2) +
          low * e (j, i) ^ 2 * (hcEmb q - algebraMap ℂ (U n) (MvPolynomial.eval (rhoVec n) q)) := by
      rw [hc, mul_sub, ← Algebra.commutes, ← Algebra.smul_def]
      abel
    rw [hs]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ ?_))
      (Submodule.mem_sup_right
        (mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal (rhoVec n) q)))
    exact Submodule.subset_span ⟨low, i, j, hlowS, hij, rfl⟩

theorem mul_sq_mem (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    rw [span_canon_eq_top]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact canon_mul_sq_mem m hij
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem Jp_le : Jp n ≤ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  refine sup_le le_sup_right (Submodule.span_le.2 ?_)
  rintro _ ⟨u, i, j, hij, rfl⟩
  exact mul_sq_mem u hij

theorem mem_sqSpan_of_mem_lowSpan_of_mem_Jp : ∀ {n : ℕ} (x : U n), x ∈ lowSpan n → x ∈ Jp n →
    x ∈ sqSpan n := by
  intro n x hx hJ
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 (Jp_le hJ)
  have ht0 : t = 0 := by
    refine eq_zero_of_mem (rhoVec n) ?_ ht
    have := Submodule.sub_mem _ hx (lowSq_le_lowSpan hs)
    rwa [add_sub_cancel_left] at this
  rw [ht0, add_zero]
  exact lowSq_le_sqSpan hs

end GlobalTheory.CompanionTheory.PresRho.LowMeet
