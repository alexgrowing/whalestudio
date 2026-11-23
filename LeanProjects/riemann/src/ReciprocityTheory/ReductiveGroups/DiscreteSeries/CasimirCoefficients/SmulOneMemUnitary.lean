import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def epsHol (p q : ℕ) : Fin (p + q) → Bool := fun i => decide ((i : ℕ) < p)

def detWt (p q : ℕ) (a b : ℤ) : Fin (p + q) → ℝ := fun i => if (i : ℕ) < p then (a : ℝ) else (b : ℝ)

def blockDet {m : ℕ} (ε : Fin m → Bool) (s : Bool) (g : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  (g.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det

def blockTr {m : ℕ} (ε : Fin m → Bool) (s : Bool) (X : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ∑ a ∈ univ.filter (fun a => ε a = s), X a a

lemma toMK_one' (ε : Fin n → Bool) : toMK (1 : KG ε) = 1 := rfl

lemma toMK_mul' {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma toMK_mem (ε : Fin n → Bool) (k : KG ε) : toMK k ∈ Kset ε := k.2

lemma blockDet_one (ε : Fin n → Bool) (s : Bool) : blockDet ε s 1 = 1 := by
  unfold blockDet
  rw [Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

lemma blockDet_mul_K {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (h : Matrix (Fin n) (Fin n) ℂ) : blockDet ε s (g * h) = blockDet ε s g * blockDet ε s h := by
  unfold blockDet
  rw [InhabA.submatrix_mul_blk s (fun i j hij => InhabA.eq_zero_of_comm hg.2 i j hij) h, Matrix.det_mul]

lemma blockDet_ne_zero {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    blockDet ε s g ≠ 0 := InhabA.det_ne_zero s hg

lemma star_blockDet_mul {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    star (blockDet ε s g) * blockDet ε s g = 1 := InhabA.star_det_mul_det s hg

lemma star_char_mul {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (a b : ℤ) :
    star (blockDet ε true g ^ a * blockDet ε false g ^ b) * (blockDet ε true g ^ a * blockDet ε false g ^ b)
      = 1 := by
  have h1 := star_blockDet_mul true hg
  have h2 := star_blockDet_mul false hg
  rw [star_mul', star_zpow₀, star_zpow₀]
  calc star (blockDet ε true g) ^ a * star (blockDet ε false g) ^ b *
        (blockDet ε true g ^ a * blockDet ε false g ^ b)
      = (star (blockDet ε true g) * blockDet ε true g) ^ a *
          (star (blockDet ε false g) * blockDet ε false g) ^ b := by
        rw [mul_zpow, mul_zpow]; ring
    _ = 1 := by rw [h1, h2, _root_.one_zpow, _root_.one_zpow, one_mul]

lemma smul_one_mem_unitary {c : ℂ} (hc : star c * c = 1) : c • (1 : ℂ →L[ℂ] ℂ) ∈ unitary (ℂ →L[ℂ] ℂ) := by
  have hc1 : (starRingEnd ℂ) c * c = 1 := hc
  have hc2 : c * (starRingEnd ℂ) c = 1 := by rw [mul_comm]; exact hc
  rw [Unitary.mem_iff]
  constructor <;> simp [star_smul, smul_smul, hc1, hc2]

lemma blockTr_add {m : ℕ} (ε : Fin m → Bool) (s : Bool) (X Y : Matrix (Fin m) (Fin m) ℂ) :
    blockTr ε s (X + Y) = blockTr ε s X + blockTr ε s Y := by
  simp [blockTr, Finset.sum_add_distrib]

lemma blockTr_smul {m : ℕ} (ε : Fin m → Bool) (s : Bool) (c : ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    blockTr ε s (c • X) = c * blockTr ε s X := by
  simp [blockTr, Finset.mul_sum]

lemma blockTr_single_diag {m : ℕ} (ε : Fin m → Bool) (s : Bool) (i : Fin m) :
    blockTr ε s (Matrix.single i i 1) = if ε i = s then 1 else 0 := by
  simp [blockTr, Matrix.single_apply]

lemma blockTr_single_ne {m : ℕ} (ε : Fin m → Bool) (s : Bool) {i j : Fin m} (hij : i ≠ j) :
    blockTr ε s (Matrix.single i j 1) = 0 := by
  unfold blockTr
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.single_apply]
  exact if_neg fun h => hij (h.1.trans h.2.symm)

def detKType (p q : ℕ) (a b : ℤ) : KType (epsHol p q) (detWt p q a b) where
  V := ℂ
  τ :=
    { toFun := fun k => ⟨(blockDet (epsHol p q) true (toMK k) ^ a *
          blockDet (epsHol p q) false (toMK k) ^ b) • (1 : ℂ →L[ℂ] ℂ),
          smul_one_mem_unitary (star_char_mul (toMK_mem _ k) a b)⟩
      map_one' := by
        apply Subtype.ext
        show (blockDet (epsHol p q) true (toMK (1 : KG (epsHol p q))) ^ a *
          blockDet (epsHol p q) false (toMK (1 : KG (epsHol p q))) ^ b) • (1 : ℂ →L[ℂ] ℂ) = 1
        rw [toMK_one', blockDet_one, blockDet_one, _root_.one_zpow, _root_.one_zpow, one_mul, one_smul]
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (blockDet (epsHol p q) true (toMK (x * y)) ^ a *
          blockDet (epsHol p q) false (toMK (x * y)) ^ b) • (1 : ℂ →L[ℂ] ℂ) =
          ((blockDet (epsHol p q) true (toMK x) ^ a * blockDet (epsHol p q) false (toMK x) ^ b) •
            (1 : ℂ →L[ℂ] ℂ)) *
          ((blockDet (epsHol p q) true (toMK y) ^ a * blockDet (epsHol p q) false (toMK y) ^ b) •
            (1 : ℂ →L[ℂ] ℂ))
        rw [toMK_mul', blockDet_mul_K true (toMK_mem _ x), blockDet_mul_K false (toMK_mem _ x),
          smul_mul_smul_comm, one_mul, mul_zpow, mul_zpow, mul_mul_mul_comm] }
  cont := by
    have hK : Continuous (fun k : KG (epsHol p q) => toMK k) :=
      (continuous_toM _).comp continuous_subtype_val
    have hd : ∀ s : Bool, Continuous (fun k : KG (epsHol p q) => blockDet (epsHol p q) s (toMK k)) :=
      fun s => (hK.matrix_submatrix _ _).matrix_det
    refine Continuous.subtype_mk ?_ _
    exact (((hd true).zpow₀ a (fun k => Or.inl (blockDet_ne_zero true (toMK_mem _ k)))).mul
      ((hd false).zpow₀ b (fun k => Or.inl (blockDet_ne_zero false (toMK_mem _ k))))).smul
      continuous_const
  irred := fun W _ => Ideal.eq_bot_or_top W
  dτ :=
    { toFun := fun X => ((a : ℂ) * blockTr (epsHol p q) true X + (b : ℂ) * blockTr (epsHol p q) false X) •
          (1 : ℂ →L[ℂ] ℂ)
      map_add' := by
        intro X Y
        rw [blockTr_add, blockTr_add, ← add_smul]
        congr 1
        ring
      map_smul' := by
        intro c X
        rw [blockTr_smul, blockTr_smul, RingHom.id_apply, smul_smul]
        congr 1
        ring }
  hasDeriv := by
    intro X _ γ hγ
    have hF : ∀ s : Bool, HasDerivAt (fun t : ℝ => blockDet (epsHol p q) s
        (NormedSpace.exp ((t : ℂ) • X))) (blockTr (epsHol p q) s X) 0 :=
      fun s => InhabA.hasDerivAt_blockDet (epsHol p q) s X
    have hF0 : ∀ s : Bool, blockDet (epsHol p q) s (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := by
      intro s
      rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, blockDet_one]
    have hZ : ∀ (s : Bool) (e : ℤ), HasDerivAt (fun t : ℝ => blockDet (epsHol p q) s
        (NormedSpace.exp ((t : ℂ) • X)) ^ e) ((e : ℂ) * blockTr (epsHol p q) s X) 0 := by
      intro s e
      have h := (hasDerivAt_zpow e _ (Or.inl (by rw [hF0 s]; exact one_ne_zero))).comp (0 : ℝ) (hF s)
      rw [hF0 s, _root_.one_zpow, mul_one] at h
      exact h
    have hP := ((hZ true a).mul (hZ false b)).smul_const (1 : ℂ →L[ℂ] ℂ)
    rw [hF0 true, hF0 false, _root_.one_zpow, _root_.one_zpow, one_mul, mul_one] at hP
    have hfun : (fun t : ℝ => ((blockDet (epsHol p q) true (toMK (γ t)) ^ a *
        blockDet (epsHol p q) false (toMK (γ t)) ^ b) • (1 : ℂ →L[ℂ] ℂ))) =
        (fun t : ℝ => (blockDet (epsHol p q) true (NormedSpace.exp ((t : ℂ) • X)) ^ a *
        blockDet (epsHol p q) false (NormedSpace.exp ((t : ℂ) • X)) ^ b) • (1 : ℂ →L[ℂ] ℂ)) := by
      funext t
      rw [hγ t]
    show HasDerivAt (fun t : ℝ => ((blockDet (epsHol p q) true (toMK (γ t)) ^ a *
        blockDet (epsHol p q) false (toMK (γ t)) ^ b) • (1 : ℂ →L[ℂ] ℂ))) _ 0
    rw [hfun]
    exact hP
  w := 1
  w_norm := by simp
  w_wt := by
    intro i
    show (((a : ℂ) * blockTr (epsHol p q) true (Matrix.single i i 1) +
      (b : ℂ) * blockTr (epsHol p q) false (Matrix.single i i 1)) • (1 : ℂ →L[ℂ] ℂ)) 1 =
      ((detWt p q a b i : ℝ) : ℂ) • (1 : ℂ)
    rw [blockTr_single_diag, blockTr_single_diag]
    by_cases h : (i : ℕ) < p
    · simp [epsHol, detWt, h]
    · simp [epsHol, detWt, h]
  w_hw := by
    intro i j hij _
    show (((a : ℂ) * blockTr (epsHol p q) true (Matrix.single i j 1) +
      (b : ℂ) * blockTr (epsHol p q) false (Matrix.single i j 1)) • (1 : ℂ →L[ℂ] ℂ)) 1 = 0
    rw [blockTr_single_ne _ _ (ne_of_lt hij), blockTr_single_ne _ _ (ne_of_lt hij)]
    simp

lemma card_filter_fin {N : ℕ} (Q : Fin N → Prop) [DecidablePred Q] (lo hi : ℕ) (hhi : hi ≤ N)
    (hQ : ∀ b : Fin N, Q b ↔ lo ≤ (b : ℕ) ∧ (b : ℕ) < hi) : (univ.filter Q).card = hi - lo := by
  have e : (univ.filter Q).map Fin.valEmbedding = Finset.Ico lo hi := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hQ b).1 hb
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, by omega⟩, (hQ _).2 ⟨h1, h2⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Nat.card_Ico]

lemma lam_hol (p q : ℕ) (a b : ℤ) (i : Fin (p + q)) :
    (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) i =
      if (i : ℕ) < p then (a : ℝ) - q / 2 + ((p : ℝ) - 1) / 2 - (i : ℕ)
      else (b : ℝ) + p / 2 + ((q : ℝ) - 1) / 2 - (((i : ℕ) : ℝ) - p) := by
  have hi := i.2
  simp only [Pi.add_apply, Pi.sub_apply, rhoN, rhoC, detWt]
  by_cases h : (i : ℕ) < p
  · have r1 : (((univ.filter fun b : Fin (p + q) => i < b ∧ epsHol p q b ≠ epsHol p q i).card : ℕ) : ℝ) = (q : ℝ) := by
      rw [card_filter_fin _ (p) (p + q) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r2 : (((univ.filter fun b : Fin (p + q) => b < i ∧ epsHol p q b ≠ epsHol p q i).card : ℕ) : ℝ) = 0 := by
      rw [card_filter_fin _ (0) (0) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r3 : (((univ.filter fun b : Fin (p + q) => i < b ∧ epsHol p q b = epsHol p q i).card : ℕ) : ℝ) = (p : ℝ) - (i : ℕ) - 1 := by
      rw [card_filter_fin _ ((i : ℕ) + 1) (p) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r4 : (((univ.filter fun b : Fin (p + q) => b < i ∧ epsHol p q b = epsHol p q i).card : ℕ) : ℝ) = ((i : ℕ) : ℝ) := by
      rw [card_filter_fin _ (0) ((i : ℕ)) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    rw [if_pos h, if_pos h, r1, r2, r3, r4]
    ring
  · have r1 : (((univ.filter fun b : Fin (p + q) => i < b ∧ epsHol p q b ≠ epsHol p q i).card : ℕ) : ℝ) = 0 := by
      rw [card_filter_fin _ (0) (0) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r2 : (((univ.filter fun b : Fin (p + q) => b < i ∧ epsHol p q b ≠ epsHol p q i).card : ℕ) : ℝ) = (p : ℝ) := by
      rw [card_filter_fin _ (0) (p) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r3 : (((univ.filter fun b : Fin (p + q) => i < b ∧ epsHol p q b = epsHol p q i).card : ℕ) : ℝ) = (p : ℝ) + q - (i : ℕ) - 1 := by
      rw [card_filter_fin _ ((i : ℕ) + 1) (p + q) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r4 : (((univ.filter fun b : Fin (p + q) => b < i ∧ epsHol p q b = epsHol p q i).card : ℕ) : ℝ) = ((i : ℕ) : ℝ) - p := by
      rw [card_filter_fin _ (p) ((i : ℕ)) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    rw [if_neg h, if_neg h, r1, r2, r3, r4]
    ring

theorem detKType_param (p q : ℕ) (a b : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    lowK (epsHol p q) (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) = detWt p q a b ∧
      ((p : ℝ) + q - 1 < (a : ℝ) - b →
        IsHCParam (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) ∧
        GapAtLeast (epsHol p q) (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q))
          ((a : ℝ) - b - (p + q) + 1) ∧
        1 ≤ q0 (epsHol p q)) := by
  refine ⟨?_, fun hab => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · funext i
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  ·
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    rw [lam_hol, lam_hol]
    have hij'' : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij'
    by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p
    · rw [if_pos hi, if_pos hj]
      linarith
    · rw [if_pos hi, if_neg hj]
      have h1 : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hi
      have h2 : (p : ℝ) ≤ (j : ℕ) := by exact_mod_cast (not_lt.1 hj)
      linarith
    · exfalso
      omega
    · rw [if_neg hi, if_neg hj]
      linarith
  · intro i
    rw [lam_hol]
    split_ifs with h
    · exact ⟨a - q - (i : ℕ), by push_cast; ring⟩
    · exact ⟨b - (i : ℕ) + p, by push_cast; ring⟩
  · intro x y hxy
    rw [lam_hol, lam_hol]
    by_cases hx : (x : ℕ) < p <;> by_cases hy : (y : ℕ) < p
    · exact absurd (by simp [epsHol, hx, hy]) hxy
    · rw [if_pos hx, if_neg hy]
      have h1 : ((x : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hx
      have h2 : (p : ℝ) ≤ (y : ℕ) := by exact_mod_cast (not_lt.1 hy)
      exact le_trans (by linarith) (le_abs_self _)
    · rw [if_neg hx, if_pos hy, abs_sub_comm]
      have h1 : ((y : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hy
      have h2 : (p : ℝ) ≤ (x : ℕ) := by exact_mod_cast (not_lt.1 hx)
      exact le_trans (by linarith) (le_abs_self _)
    · exact absurd (by simp [epsHol, hx, hy]) hxy
  · have hP : pOf (epsHol p q) = p := by
      unfold pOf
      rw [card_filter_fin _ 0 p (by omega) fun b => by
        have := b.2
        simp only [epsHol, decide_eq_true_eq]
        omega]
      omega
    have hQ : qOf (epsHol p q) = q := by
      unfold qOf
      rw [card_filter_fin _ p (p + q) le_rfl fun b => by
        have := b.2
        simp only [epsHol, decide_eq_false_iff_not]
        omega]
      omega
    simp only [q0, hP, hQ]
    omega

end ReciprocityTheory.ChartRestriction.DS.S7
