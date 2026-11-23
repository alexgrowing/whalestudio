import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SegDistsLtG

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section Deg

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem window_entry_le_two_mul_a (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (l : Fin X.s) :
    (a l : ℝ) ≤ 2 * X.L.a := by
  have h2 := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hT l)).2
  have h3 : (a l : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h2
  exact (h3.trans (Nat.floor_le hS.hF.win0)).trans hS.hF.win_le

theorem r5 : (5 : ℝ) ≤ (X.r : ℝ) + 1 := by
  have : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hS.hF.m4
  show (5 : ℝ) ≤ (X.L.m : ℝ) + 1
  linarith

theorem b_small : 5 / 2 * X.L.b' ≤ X.L.a / 8 := by
  have h1 := hS.kb
  have h2 := r5 hS
  have hb := hS.hF.b0
  nlinarith

theorem chain_wt (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) ≠ 2 * X.s) :
    ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) * ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) ≤ 2 * X.L.a := by
  have hA : ∀ l, (coarseA X.p (X.S C0 CE1 CE2) b l : ℝ) * ((X.S C0 CE1 CE2).P X.p l : ℝ) ≤ 2 * X.L.a := fun l =>
    (coarseA_upper hS b l).trans (by have := b_small hS; have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _; linarith)
  have hC : ∀ l, (coarseC X.p (X.S C0 CE1 CE2) a b l : ℝ) * ((X.S C0 CE1 CE2).P X.p l : ℝ) ≤ 2 * X.L.a := by
    intro l
    have h1 : coarseC X.p (X.S C0 CE1 CE2) a b l * (X.S C0 CE1 CE2).P X.p l ≤ a l :=
      (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
    have h2 : ((coarseC X.p (X.S C0 CE1 CE2) a b l * (X.S C0 CE1 CE2).P X.p l : ℕ) : ℝ) ≤ (a l : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (window_entry_le_two_mul_a hS a hT l)
  have hP0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) := Nat.cast_nonneg _
  have key : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ coarseA X.p (X.S C0 CE1 CE2) b (topOf q hq) ∨
      (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ coarseC X.p (X.S C0 CE1 CE2) a b (topOf q hq) := by
    unfold segChain
    dsimp only
    rw [dif_neg hq]
    split_ifs with h2 h3 h3
    · exact Or.inl (hK.2.2.1 _ h3).2.1
    · exact Or.inl (hK.2.1 _ (not_lt.mp h3)).1
    · exact Or.inr (Nat.sub_le _ _)
    · exact Or.inr le_rfl
  rcases key with h | h
  · have : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) b (topOf q hq) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_right this hP0).trans (hA _)
  · have : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ (coarseC X.p (X.S C0 CE1 CE2) a b (topOf q hq) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_right this hP0).trans (hC _)

theorem oplus_le (b : SegBlock X.s X.r) (a : Fin X.s → ℕ) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) :
    (b.oPlus : ℝ) ≤ 2 * X.L.a := by
  have h0 := hK.2.2.2
  unfold Oplus at h0
  have hp1 : 1 ≤ X.p := X.std.1.prime.one_lt.le
  have hB : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ 5 / 2 * X.L.b' := hS.bTop
  have hcap := cap_le (p := X.p) (X.S C0 CE1 CE2) b hp1 hS.E0 (5 / 2 * X.L.b') hB X.s
  have hr5 := r5 hS
  have hs : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hS.hF.s_le
  have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
  have hb := hS.hF.b0
  have hkb := hS.kb
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hLa0 := hS.hF.La0
  have hLa : X.L.La C0 / ((X.r : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith [hS.La4]
  have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
  have hp5 : (5 : ℝ) ≤ (X.p : ℝ) := by nlinarith
  have h4 : 4 / (X.p : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsum : (∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ)) ≤ (X.s : ℝ) * (2 * X.L.a / X.p) := by
    have : ∀ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ 2 * X.L.a / X.p := by
      intro i
      have hP : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p i : ℝ) := by exact_mod_cast p_le_P i
      show 2 * (X.L.a : ℝ) / _ ≤ _
      exact div_le_div_of_nonneg_left (by positivity) hp0 hP
    calc _ ≤ ∑ _i : Fin X.s, 2 * (X.L.a : ℝ) / X.p := Finset.sum_le_sum fun i _ => this i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsp : (X.s : ℝ) * (2 * X.L.a / X.p) ≤ X.L.a / 5 := by
    rw [mul_div_assoc', div_le_div_iff₀ hp0 (by norm_num)]
    have h10 : 10 * (X.s : ℝ) ≤ (X.p : ℝ) := by nlinarith
    have := mul_le_mul_of_nonneg_left h10 ha0
    linarith
  have hsum0 : 0 ≤ ∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hmid : (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 / 2 := by
    show X.L.La C0 / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 / 2
    linarith
  have hmid0 : 0 ≤ (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 := by
    show 0 ≤ X.L.La C0 / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2
    positivity
  have hT2 : ((X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2) *
      ∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.a / 10 := by
    have := mul_le_mul hmid (hsum.trans hsp) hsum0 (by norm_num)
    linarith
  have hBp : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := hS.hF.bT_le _ (segNext_mem X.L.TT X.j)
  have hT3 : (X.S C0 CE1 CE2).La * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.r : ℝ) + 1) ≤ X.L.a / 10 := by
    have e : (X.S C0 CE1 CE2).La * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.r : ℝ) + 1) =
        X.L.La C0 / ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).bPlus : ℝ) := by
      show X.L.La C0 * _ / _ = _
      ring
    rw [e]
    have h5 := b_small hS
    have h6 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).bPlus : ℝ) := Nat.cast_nonneg _
    have h7 : X.L.La C0 / ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 1 / 4 * (5 / 2 * X.L.b') :=
      mul_le_mul hLa hBp h6 (by norm_num)
    linarith
  have hsB : (X.s : ℝ) * (5 / 2 * X.L.b') ≤ X.L.a / 2 := by
    have h1 : (X.s : ℝ) ≤ ((X.r : ℝ) + 1) / 2 := by linarith
    have h2 : (X.s : ℝ) * (5 / 2 * X.L.b') ≤ ((X.r : ℝ) + 1) / 2 * (5 / 2 * X.L.b') :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith
  have ha : (X.S C0 CE1 CE2).a = X.L.a := rfl
  rw [ha] at hcap
  linarith

theorem lLL_deg_le_chain (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (q : Fin (2 * X.s + 1)) :
    (lLL C0 CE1 CE2 X a b x).deg q ≤ (segChain X.p (X.S C0 CE1 CE2) a b).deg q :=
  (Nat.sub_le _ _).trans (Nat.sub_le _ _)

theorem lLL_deg_le (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X) (q : Fin (2 * X.s + 1)) :
    (lLL C0 CE1 CE2 X a b x).deg q ≤ 2 * X.L.a := by
  have h1 := lLL_deg_le_chain hS a b x q
  have h2 : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ 2 * X.L.a := by
    by_cases hq : (q : ℕ) = 2 * X.s
    · have e := segChain_deg_last (p := X.p) (X.S C0 CE1 CE2) a b q hq
      rw [e]
      exact oplus_le hS b a hK
    · have hw := chain_wt hS a hT b hK q hq
      have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) := by exact_mod_cast hS.P1 _
      have h0 : (0 : ℝ) ≤ ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) := Nat.cast_nonneg _
      nlinarith
  have h3 : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ 2 * X.L.a := by exact_mod_cast h2
  omega

end Deg

end Formalism.MainNotions.G.SymmetricFormBlocks

end
