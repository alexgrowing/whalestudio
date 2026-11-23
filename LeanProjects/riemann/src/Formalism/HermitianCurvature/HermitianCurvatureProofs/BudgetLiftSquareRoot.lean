import Mathlib
import Formalism.HermitianCurvature.StatementTA

open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace Formalism.FourierDecayAlt.P.BudgetLiftBounds

theorem bud_lift (Kl r i n : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ r + 1) (hn : n ≤ 4 * Kl * (r + 1 - i)) :
    n + Kl ≤ 4 * Kl * (r + 1) := by
  generalize r + 1 = M at *
  obtain ⟨d, rfl⟩ : ∃ d, M = i + d := ⟨M - i, by omega⟩
  have e : i + d - i = d := by omega
  rw [e] at hn
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  nlinarith [Nat.zero_le (Kl * j), Nat.zero_le Kl]

theorem bud_one (Kl r i n n' : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ r + 1) (hn : n ≤ 4 * Kl * (r + 1 - i))
    (hn' : n' ≤ n + Kl) :
    n' + Kl ≤ 4 * Kl * (r + 1 - (i - 1)) ∧ 4 * Kl * (r + 1 - (i - 1)) ≤ 4 * Kl * (r + 1) := by
  generalize r + 1 = M at *
  obtain ⟨d, rfl⟩ : ∃ d, M = i + d := ⟨M - i, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have e : j + 1 + d - (j + 1) = d := by omega
  have e' : j + 1 + d - (j + 1 - 1) = d + 1 := by omega
  rw [e] at hn
  rw [e']
  constructor
  · nlinarith [Nat.zero_le Kl]
  · nlinarith [Nat.zero_le (Kl * j)]

theorem bud_block (Kl r i s n n' : ℕ) (hs : 2 ≤ s) (hsi : s ≤ i) (h2 : i ≤ r + 1)
    (hn : n ≤ 4 * Kl * (r + 1 - i)) (hn' : n' ≤ n + Kl) :
    n' + (s + 1) * Kl ≤ 4 * Kl * (r + 1 - (i - s)) ∧
      4 * Kl * (r + 1 - (i - s)) ≤ 4 * Kl * (r + 1) := by
  generalize r + 1 = M at *
  obtain ⟨d, rfl⟩ : ∃ d, M = i + d := ⟨M - i, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + s := ⟨i - s, by omega⟩
  have e : j + s + d - (j + s) = d := by omega
  have e' : j + s + d - (j + s - s) = d + s := by omega
  rw [e] at hn
  rw [e']
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
  constructor
  · nlinarith [Nat.zero_le (Kl * u), Nat.zero_le Kl]
  · nlinarith [Nat.zero_le (Kl * j)]

theorem sizes_tie {E : Type} [Field E] (D : Data E) (Pat3 : Type) [Fintype Pat3] (c1 : E → ℝ)
    (c3 : ℕ → E → ℝ) (ep1 : ℝ) (ep3 bd4 : ℕ → ℝ) (ep a : ℝ) (i : ℕ)
    (h : LevelSizes D Pat3 c1 c3 ep1 ep3 bd4 ep a i) : 0 ≤ ep1 ∧ 1 + ep1 ≤ (1 + ep) ^ 2 := by
  obtain ⟨h1, _, h3, h4, _⟩ := h
  have e1 : 0 ≤ ep1 := by simpa using h1.2 ∅ (by simp)
  refine ⟨e1, le_trans ?_ h4⟩
  have : 0 ≤ (Fintype.card Pat3 : ℝ) * ep3 1 := mul_nonneg (Nat.cast_nonneg _) h3
  nlinarith

theorem isPt_PT {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    cases n with
    | zero =>
      simp [PT] at hp; subst hp; exact ⟨by simp [lvl], by simp⟩
    | succ n =>
      rw [PT] at hp
      simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range] at hp
      obtain ⟨m, hm, h, hh, t, ht, rfl⟩ := hp
      have h0 := ih m (by omega) h hh
      refine ⟨?_, ?_⟩
      · have := h0.1
        simp only [lvl] at this
        simp [lvl, Formalism.FourierDecayAlt.TA.ext, this]; omega
      · intro b hb
        simp only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact h0.2 b hb
        · exact ⟨by simp; omega, hNZ _ _ t ht⟩

theorem le_wsup {W : Type} [Finite W] (len : W → ℕ) (B : ℕ) (g : W → ℝ) (w : W) (h : len w ≤ B) :
    g w ≤ wsup len B g :=
  le_ciSup (f := fun w : {w // len w ≤ B} => g w.1) (Set.finite_range _).bddAbove ⟨w, h⟩

theorem wsup_le {W : Type} (len : W → ℕ) (B : ℕ) (g : W → ℝ) (M : ℝ) (w0 : W) (h0 : len w0 ≤ B)
    (h : ∀ w, len w ≤ B → g w ≤ M) : wsup len B g ≤ M := by
  have : Nonempty {w // len w ≤ B} := ⟨⟨w0, h0⟩⟩
  exact ciSup_le fun w => h w.1 w.2

theorem sqrt_le_of {x c d L : ℝ} (hx : x ≤ c * L) (hc0 : 0 ≤ c) (hcd : c ≤ d ^ 2) (hd : 0 ≤ d) :
    √x ≤ d * √L := by
  rcases le_or_gt 0 L with hL | hL
  · have : x ≤ d ^ 2 * L := le_trans hx (mul_le_mul_of_nonneg_right hcd hL)
    calc √x ≤ √(d ^ 2 * L) := Real.sqrt_le_sqrt this
      _ = d * √L := by rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd]
  · have : x ≤ 0 := le_trans hx (mul_nonpos_of_nonneg_of_nonpos hc0 hL.le)
    rw [Real.sqrt_eq_zero_of_nonpos this]
    exact mul_nonneg hd (Real.sqrt_nonneg _)

theorem exists_reps {E : Type} [AddCommGroup E] [DecidableEq E] (L : AddSubgroup E) (S : Finset E) :
    ∃ R : Finset E, (∀ t ∈ S, ∃ t0 ∈ R, t - t0 ∈ L) ∧ (∀ x ∈ R, ∀ y ∈ R, x - y ∈ L → x = y) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a S _ ih =>
    obtain ⟨R, h1, h2⟩ := ih
    by_cases h : ∃ t0 ∈ R, a - t0 ∈ L
    · refine ⟨R, ?_, h2⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact h
      · exact h1 t ht
    · refine ⟨insert a R, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact ⟨t, Finset.mem_insert_self _ _, by simp⟩
        · obtain ⟨t0, ht0, h3⟩ := h1 t ht
          exact ⟨t0, Finset.mem_insert_of_mem ht0, h3⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with hxa | hxR
        · rcases Finset.mem_insert.mp hy with hya | hyR
          · rw [hxa, hya]
          · exact absurd ⟨y, hyR, hxa ▸ hxy⟩ h
        · rcases Finset.mem_insert.mp hy with hya | hyR
          · exact absurd ⟨x, hxR, by have := L.neg_mem hxy; rw [hya] at this; simpa using this⟩ h
          · exact h2 x hxR y hyR hxy

theorem oneLevelOfSteps : OneLevelOfSteps := by
  intro hSplit hOff hTop hDC hC1 hCS
  intro E _ _ H _ _ W _ len Kl D Sg Φ tr Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 ep a i
    hNZ h1 hi hep ha hK hA2 hA13 hE hEst hSz
  obtain ⟨hPo, h72, h73, h74⟩ := hEst
  obtain ⟨hep1, htie⟩ := sizes_tie _ _ _ _ _ _ _ _ _ _ hSz
  obtain ⟨hL1, hL3, hep3, hs1, hs2⟩ := hSz
  obtain ⟨he0, he1⟩ := hE i h1 hi
  have hP : (0:ℝ) ≤ Fintype.card Pat3 := Nat.cast_nonneg _

  have hD1 : ∀ w', len w' + Kl ≤ 4 * Kl * (D.r + 1 - (i - 1)) → len w' + Kl ≤ 4 * Kl * (D.r + 1) →
      Diag D Sg Φ w' i 1 ≤ (1 + D.e i) * (1 + ep1) * lsup D len Kl Sg Φ (i - 1) := by
    intro w' hb hbN
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La i 1) (Sg i 1)
    have a1 := hDC E H W D Sg Φ w' i 1 R hNZ le_rfl h1 hi hA13 hR1 hR2
    have a2 := hC1 E H W len Kl (4 * Kl * (D.r + 1)) D Sg Φ tr Pat1 pat1 c1 ep1 i w' R hNZ h1 hi hK hA13 hE
      hPo h72 hL1 hbN hR2
    have a3 : Slev D Sg Φ w' (i - 1) ≤ lsup D len Kl Sg Φ (i - 1) :=
      le_wsup len _ (fun w => Slev D Sg Φ w (i - 1)) w' (le_trans (Nat.le_add_right _ _) hb)
    have a4 : wsup len (len w' + Kl) (fun w'' => Slev D Sg Φ w'' (i - 1)) ≤ lsup D len Kl Sg Φ (i - 1) :=
      wsup_le len _ _ _ w' (Nat.le_add_right _ _) fun w'' hw'' =>
        le_wsup len _ (fun w => Slev D Sg Φ w (i - 1)) w'' (le_trans hw'' hb)
    calc Diag D Sg Φ w' i 1 ≤ _ := le_trans a1 a2
      _ ≤ (1 + D.e i) * (lsup D len Kl Sg Φ (i - 1) + ep1 * lsup D len Kl Sg Φ (i - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact add_le_add a3 (mul_le_mul_of_nonneg_left a4 hep1)
      _ = _ := by ring

  have hDs : ∀ s ∈ Icc 2 i, ∀ w', len w' + (s + 1) * Kl ≤ 4 * Kl * (D.r + 1 - (i - s)) →
      len w' + (s + 1) * Kl ≤ 4 * Kl * (D.r + 1) →
      Diag D Sg Φ w' i s ≤ (1 + D.e i) * bd4 s * lsup D len Kl Sg Φ (i - s) := by
    intro s hs w' hb hbN
    obtain ⟨hs2', hsi⟩ := Finset.mem_Icc.mp hs
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La i s) (Sg i s)
    have a1 := hDC E H W D Sg Φ w' i s R hNZ (by omega) hsi hi hA13 hR1 hR2
    have a2 := hCS E H W len Kl (4 * Kl * (D.r + 1)) D Sg Φ (bd4 s) i s w' R hNZ hs2' hsi hi hK hA13 hE
      (hs2 s hs).1 (h74 s hs) hbN hR2
    have a4 : wsup len (len w' + (s + 1) * Kl) (fun w'' => Slev D Sg Φ w'' (i - s)) ≤
        lsup D len Kl Sg Φ (i - s) :=
      wsup_le len _ _ _ w' (Nat.le_add_right _ _) fun w'' hw'' =>
        le_wsup len _ (fun w => Slev D Sg Φ w (i - s)) w'' (le_trans hw'' hb)
    exact le_trans (le_trans a1 a2)
      (mul_le_mul_of_nonneg_left a4 (mul_nonneg (by linarith) (hs2 s hs).1))

  have hSch : ∀ s ∈ Icc 1 i, ¬ (i = D.r + 1 ∧ s = 1) → ∀ w, len w ≤ 4 * Kl * (D.r + 1 - i) → ∀ M : ℝ,
      (∀ w', len w' ≤ len w + Kl → Diag D Sg Φ w' i s ≤ M) →
      Ssplit D Sg Φ w i s ≤ (1 + Fintype.card Pat3 * ep3 s) * M := by
    intro s hs hnt w hw M hM
    obtain ⟨hs1', hsi⟩ := Finset.mem_Icc.mp hs
    have hl := hL3 s hs hnt
    have hep3s : 0 ≤ ep3 s := by simpa using hl.2 ∅ (by simp)
    have b1 := hOff E H W len Kl (4 * Kl * (D.r + 1)) D Sg Φ Pat3 (pat3 s) (c3 s) (ep3 s) i s w hNZ hs1' hsi hi
      hK hA2 (h73 s hs hnt) hl (bud_lift Kl D.r i (len w) h1 hi hw)
    have b2 : wsup len (len w + Kl) (fun w' => Diag D Sg Φ w' i s) ≤ M :=
      wsup_le len _ _ _ w (Nat.le_add_right _ _) hM
    have b3 := hM w (Nat.le_add_right _ _)
    have b4 := mul_le_mul_of_nonneg_left b2 (mul_nonneg hP hep3s)
    calc Ssplit D Sg Φ w i s ≤ _ := b1
      _ ≤ M + Fintype.card Pat3 * ep3 s * M := add_le_add b3 b4
      _ = _ := by ring
  have hd1 : ((1 + ep) * √(1 + D.e i)) ^ 2 = (1 + ep) ^ 2 * (1 + D.e i) := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]

  have key1 : ∀ w, len w ≤ 4 * Kl * (D.r + 1 - i) →
      √(Ssplit D Sg Φ w i 1) ≤ (1 + ep) * √(1 + D.e i) * √(lsup D len Kl Sg Φ (i - 1)) := by
    intro w hw
    have hd0 : 0 ≤ (1 + ep) * √(1 + D.e i) := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    by_cases htop : i = D.r + 1
    · have c1' := hTop E H W D Sg Φ w hNZ hA2
      rw [← htop] at c1'
      obtain ⟨q1, q2⟩ := bud_one Kl D.r i (len w) (len w) h1 hi hw (Nat.le_add_right _ _)
      have c2 := hD1 w q1 (le_trans q1 q2)
      rw [← c1'] at c2
      refine sqrt_le_of c2 (mul_nonneg (by linarith) (by linarith)) ?_ hd0
      rw [hd1]
      nlinarith
    · have hnt : ¬ (i = D.r + 1 ∧ (1:ℕ) = 1) := fun h => htop h.1
      have c2 := hSch 1 (Finset.mem_Icc.mpr ⟨le_rfl, h1⟩) hnt w hw _ (fun w' hw' => by
        obtain ⟨q1, q2⟩ := bud_one Kl D.r i (len w) (len w') h1 hi hw hw'
        exact hD1 w' q1 (le_trans q1 q2))
      rw [← mul_assoc] at c2
      refine sqrt_le_of c2 (mul_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))) ?_ hd0
      rw [hd1]
      nlinarith

  have keys : ∀ w, len w ≤ 4 * Kl * (D.r + 1 - i) → ∀ s ∈ Icc 2 i,
      √(Ssplit D Sg Φ w i s) ≤ a ^ (s - 1) * √(lsup D len Kl Sg Φ (i - s)) := by
    intro w hw s hs
    obtain ⟨hs2', hsi⟩ := Finset.mem_Icc.mp hs
    have hs' : s ∈ Icc 1 i := Finset.mem_Icc.mpr ⟨by omega, hsi⟩
    have hnt : ¬ (i = D.r + 1 ∧ s = 1) := fun h => by omega
    have hep3s : 0 ≤ ep3 s := by simpa using (hL3 s hs' hnt).2 ∅ (by simp)
    have c2 := hSch s hs' hnt w hw _ (fun w' hw' => by
      obtain ⟨q1, q2⟩ := bud_block Kl D.r i s (len w) (len w') hs2' hsi hi hw hw'
      exact hDs s hs w' q1 (le_trans q1 q2))
    rw [← mul_assoc] at c2
    refine sqrt_le_of c2 (mul_nonneg (by positivity) (mul_nonneg (by linarith) (hs2 s hs).1)) ?_
      (pow_nonneg ha _)
    rw [← pow_mul, mul_comm (s - 1) 2, ← mul_assoc]
    exact (hs2 s hs).2

  have hRHS0 : 0 ≤ (1 + ep) * √(1 + D.e i) * √(lsup D len Kl Sg Φ (i - 1)) +
        ∑ s ∈ Icc 2 i, a ^ (s - 1) * √(lsup D len Kl Sg Φ (i - s)) := by
    refine add_nonneg (mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg ha _) (Real.sqrt_nonneg _))
  have hw : ∀ w, len w ≤ 4 * Kl * (D.r + 1 - i) → √(Slev D Sg Φ w i) ≤
      (1 + ep) * √(1 + D.e i) * √(lsup D len Kl Sg Φ (i - 1)) +
        ∑ s ∈ Icc 2 i, a ^ (s - 1) * √(lsup D len Kl Sg Φ (i - s)) := by
    intro w hw
    have hPSD : PSDOn (PT Sg i) (D.K i) := hK.2 i hi _ (fun p hp => isPt_PT Sg hNZ i p hp)
    have h0 := hSplit E H W D Sg Φ w i hNZ h1 hPSD
    have hIcc : Icc 1 i = insert 1 (Icc 2 i) := by ext x; simp; omega
    rw [hIcc, Finset.sum_insert (by simp)] at h0
    exact le_trans h0 (add_le_add (key1 w hw) (Finset.sum_le_sum fun s hs => keys w hw s hs))
  rw [Real.sqrt_le_iff]
  refine ⟨hRHS0, ?_⟩
  by_cases hne : Nonempty {w // len w ≤ 4 * Kl * (D.r + 1 - i)}
  · unfold lsup wsup
    exact ciSup_le fun w => ((Real.sqrt_le_iff).1 (hw w.1 w.2)).2
  · unfold lsup wsup
    have := not_nonempty_iff.mp hne
    rw [Real.iSup_of_isEmpty]
    positivity

theorem le_sq_sqrt (x : ℝ) : x ≤ (√x) ^ 2 := by
  rcases le_or_gt 0 x with h | h
  · rw [Real.sq_sqrt h]
  · exact le_trans h.le (sq_nonneg _)

theorem slev_zero {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {W : Type} (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W)
    (h : D.K 0 [] [] = 1) : Slev D Sg Φ w 0 = ‖Φ w []‖ ^ 2 := by
  unfold Slev gram
  have : PT Sg 0 = {[]} := by simp [PT]
  rw [this]
  simp only [Finset.sum_singleton, h, one_mul]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem reductionOfSteps : ReductionOfSteps := by
  intro hOL hEps hA4 hJ C₀ hC₀
  obtain ⟨C'J, CJ, hJ'⟩ := hJ C₀ hC₀
  refine ⟨max C'J 1, CJ, ?_⟩
  intro E _ _ H _ _ _ W _ len Kl f Θ D Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 Φ tr w0 V jn ρ c
    hKl hf hΘ hr hK hA2 hA13 hE hSz hEst hEn hw0 hV hRow hSum
  have hΘJ : C'J ≤ Θ := le_trans (le_max_left _ _) hΘ
  have hΘ1 : 1 ≤ Θ := le_trans (le_max_right _ _) hΘ
  have hΘ0 : 0 < Θ := by linarith
  have hC0 : 0 < C₀ := by linarith
  have hep0 : 0 ≤ (C₀ * Θ ^ (-((Kl : ℝ) - 5 / 2))) ^ f := by positivity
  have ha0 : 0 ≤ (C₀ / Θ) ^ f := by positivity
  have main : ∀ Sg : ℕ → ℕ → Finset E, NZSg Sg → ∀ eps : ℝ, 0 < eps →
      (gram (D.K (D.r + 1)) (Φ eps w0) (PT Sg (D.r + 1))).re ≤
        ((1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) *
          wsup len (4 * Kl * (D.r + 1)) (fun w => ‖Φ eps w []‖ ^ 2) := by
    intro Sg hNZ eps heps
    have hrec := hJ' (Kl : ℝ) Θ f D.r (fun i => max (D.e i) 0)
      (fun i => √(lsup D len Kl Sg (Φ eps) i))
      (by exact_mod_cast hKl) hf hΘJ hr (fun i => le_max_right _ _) (fun i => Real.sqrt_nonneg _)
      (by
        intro i h1 hi
        have h := hOL E H W len Kl D Sg (Φ eps) (tr eps i) Pat1 Pat3 (pat1 i) (pat3 i) (c1 i) (c3 i)
          (ep1 i) (ep3 i) (bd4 i) _ _ i hNZ h1 hi hep0 ha0 hK hA2 hA13 hE
          (hEst eps heps i (mem_Icc.mpr ⟨h1, hi⟩)) (hSz i (mem_Icc.mpr ⟨h1, hi⟩))
        have he : max (D.e i) 0 = D.e i := max_eq_left (hE i h1 hi).1
        simp only [he]
        exact h)
    have hprod : (∏ i ∈ Icc 1 (D.r + 1), (1 + max (D.e i) 0)) = ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      obtain ⟨h1, h2⟩ := mem_Icc.mp hi
      rw [max_eq_left (hE i h1 h2).1]
    rw [hprod] at hrec
    have h0 : lsup D len Kl Sg (Φ eps) 0 =
        wsup len (4 * Kl * (D.r + 1)) (fun w => ‖Φ eps w []‖ ^ 2) := by
      unfold lsup
      rw [Nat.sub_zero]
      congr 1
      funext w
      exact slev_zero D Sg (Φ eps) w hK.1
    have h0nn : 0 ≤ lsup D len Kl Sg (Φ eps) 0 := by
      rw [h0]
      exact le_trans (sq_nonneg _)
        (le_wsup len _ (fun w => ‖Φ eps w []‖ ^ 2) w0 (by rw [hw0]; exact Nat.zero_le _))
    rw [Real.sq_sqrt h0nn, h0] at hrec
    have htop : Slev D Sg (Φ eps) w0 (D.r + 1) ≤ lsup D len Kl Sg (Φ eps) (D.r + 1) :=
      le_wsup len _ (fun w => Slev D Sg (Φ eps) w (D.r + 1)) w0 (by rw [hw0]; exact Nat.zero_le _)
    exact le_trans htop (le_trans (le_sq_sqrt _) hrec)
  have lim : ∀ Sg : ℕ → ℕ → Finset E, NZSg Sg → (gram (D.K (D.r + 1)) V (PT Sg (D.r + 1))).re ≤
      ((1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) * jn := by
    intro Sg hNZ
    exact hEps E H W len (D.K (D.r + 1)) (PT Sg (D.r + 1)) Φ V w0 (4 * Kl * (D.r + 1)) _ jn
      (by rw [hw0]; exact Nat.zero_le _) (main Sg hNZ) hEn
      (fun p hp => hV p (isPt_PT Sg hNZ _ p hp))
  exact hA4 E H (D.r + 1) (D.K (D.r + 1)) V ρ c _ lim hRow hSum

end Formalism.FourierDecayAlt.P.BudgetLiftBounds

namespace Formalism.FourierDecayAlt.P

theorem one_level_inequality_of_parts : Formalism.FourierDecayAlt.TA.OneLevelOfSteps := BudgetLiftBounds.oneLevelOfSteps

theorem reduction_bound_of_one_level : Formalism.FourierDecayAlt.TA.ReductionOfSteps := BudgetLiftBounds.reductionOfSteps

end Formalism.FourierDecayAlt.P
