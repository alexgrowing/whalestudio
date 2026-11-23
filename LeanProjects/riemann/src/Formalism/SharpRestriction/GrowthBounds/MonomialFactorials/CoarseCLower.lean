import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.KappaZeroNonneg

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

structure SegFacts (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : Prop where
  hF : HIFacts C0 X
  kP : ∀ i, ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.b'
  P1 : ∀ i, 1 ≤ (X.S C0 CE1 CE2).P X.p i
  PQ : ∀ i, (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).Qj X.p
  La4 : 4 * X.L.La C0 < (X.r : ℝ) + 1
  E0 : 0 ≤ (X.S C0 CE1 CE2).E0
  bTop : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ 5 / 2 * X.L.b'
  kb : ((X.r : ℝ) + 1) * X.L.b' ≤ (X.L.a : ℝ) / 4
  Y1 : 1 ≤ X.L.Y
  xa0 : 0 ≤ X.xa
  xa : X.xa ≤ 2 * X.L.J0 C0

theorem segFacts {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hCb : 1 ≤ Cb) (hCD : 0 ≤ CD) (hCE1 : 0 ≤ CE1)
    (hCE2 : 0 ≤ CE2) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : SegFacts C0 CE1 CE2 X := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X (by linarith) hH
  obtain ⟨h0, -, hxa0, hxa, -, -, -, -, -, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, hseg, hN1, hm, hLa8, hb0, hbl, hbh, h12, hbw, hYb, hk2, hlog, hde, hpa, hCk,
    hband, hccl0, hccl1, hDLP, hcs, hbig⟩ := h0
  have hk : X.L.k = (X.L.m : ℝ) + 1 := rfl
  have hp25 := p25 hF
  have hp1 : 1 ≤ X.L.p := by
    have : (1 : ℝ) ≤ (X.L.p : ℝ) := by linarith
    exact_mod_cast this
  have hN : (1 : ℝ) ≤ X.L.N := by
    have : 1 ≤ X.L.TT.card := Finset.card_pos.2 ⟨s0, hs0⟩
    show (1 : ℝ) ≤ (X.L.TT.card : ℝ)
    exact_mod_cast this
  have hQ1 : (1 : ℝ) ≤ X.L.Q := by
    show (1 : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'
    exact one_le_pow₀ (by linarith)
  have hk1 : (1 : ℝ) ≤ X.L.k := by rw [hk]; have : (0 : ℝ) ≤ X.L.m := Nat.cast_nonneg _; linarith
  have hlogb : 0 ≤ Real.logb X.L.p X.L.a := Real.logb_nonneg (by linarith) hF.a1
  have hDLP0 : 0 ≤ X.L.DLP := by
    refine le_trans ?_ hDLP
    have : (0 : ℝ) ≤ (X.L.N1 : ℝ) ^ 5 + X.L.k ^ 3 := by positivity
    have : 0 ≤ X.L.N := by linarith
    positivity
  have hM : (1 : ℝ) ≤ X.L.cs + X.L.N * X.L.ccl + X.L.n' * X.L.ccl := by
    have h1 : 0 ≤ X.L.N * X.L.ccl := mul_nonneg (by linarith) hccl0
    have h2 : 0 ≤ (X.L.n' : ℝ) * X.L.ccl := mul_nonneg (Nat.cast_nonneg _) hccl0
    linarith
  have hkQ : X.L.k * X.L.Q ≤ X.L.b' := by
    refine le_trans ?_ hbig
    have e1 : X.L.k ≤ X.L.k ^ 3 := le_self_pow₀ hk1 (by norm_num)
    have e2 : X.L.Q ≤ X.L.Q ^ 4 := le_self_pow₀ hQ1 (by norm_num)
    calc X.L.k * X.L.Q = 1 * X.L.k * 1 * X.L.Q * 1 * 1 := by ring
      _ ≤ Cb * X.L.k ^ 3 * X.L.N * X.L.Q ^ 4 * (X.L.cs + X.L.N * X.L.ccl + X.L.n' * X.L.ccl) * X.L.Y := by
          gcongr
  have hPQ : ∀ i, (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).Qj X.p := fun i =>
    Nat.pow_le_pow_right (lt_of_lt_of_le zero_lt_one hp1) (Nat.sub_le _ _)
  have hQj : ((X.S C0 CE1 CE2).Qj X.p : ℝ) ≤ X.L.Q := by
    show ((X.L.p ^ segG X.L.TT X.j : ℕ) : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'
    push_cast
    exact pow_le_pow_right₀ (by exact_mod_cast hp1) (hseg X.j).1
  have hE0 : 0 ≤ (X.S C0 CE1 CE2).E0 := by
    show 0 ≤ errorTermBound CE1 CE2 X.L.p X.L.k X.L.N1 X.L.Q X.L.c X.L.a X.L.b' (X.L.La C0)
    unfold errorTermBound
    have h1 := hF.La0
    have h2 := hF.b0.le
    have h3 : (0 : ℝ) ≤ X.L.k := by linarith
    have h4 : (0 : ℝ) ≤ X.L.Q := by linarith
    positivity
  refine ⟨hF, fun i => ?_, fun i => Nat.one_le_pow _ _ (lt_of_lt_of_le zero_lt_one hp1), hPQ, ?_, hE0, fun i => ?_, ?_, hY, hxa0, hxa⟩
  · have h1 : ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.Q :=
      le_trans (by exact_mod_cast hPQ i) hQj
    have h2 : X.L.k * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.b' :=
      le_trans (mul_le_mul_of_nonneg_left h1 (by linarith)) hkQ
    exact h2
  · have hYb2 : 2 ≤ X.L.Yb := le_trans hCYb hYb
    have : 4 * X.L.La C0 ≤ 2 * X.L.Yb * X.L.N * X.L.La C0 := by
      have h0 := hF.La0
      have hYN : 2 ≤ X.L.Yb * X.L.N := by nlinarith only [hYb2, hN]
      have := mul_le_mul_of_nonneg_right hYN h0
      linarith only [this]
    have h2 : 4 * X.L.La C0 < X.L.k := by linarith
    exact h2
  · exact hF.bT_le _ (segPos_mem X.L.TT X.j i)
  · have h1 := hF.b_lt
    have h2 : ((X.r : ℝ) + 1) ^ 2 ≤ (X.L.p : ℝ) := hF.p_ge
    have hm4 : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
    have hb := hF.b0
    have h4 : 4 * ((X.L.m : ℝ) + 1) ≤ (X.L.p : ℝ) := by nlinarith only [h2, hm4]
    have h5 := mul_le_mul_of_nonneg_right h4 hb.le
    have h3 : ((X.L.m : ℝ) + 1) * X.L.b' ≤ (X.L.a : ℝ) / 4 := by linarith only [h5, h1]
    exact h3

section Coarse

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem coarseC_lower (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (hD : DigitsOK X.p (X.S C0 CE1 CE2) aTop b)
    (i : Fin X.s) :
    (aTop i : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤
      (coarseC X.p (X.S C0 CE1 CE2) aTop b i : ℝ) * ((X.S C0 CE1 CE2).P X.p i : ℝ) := by
  set P := (X.S C0 CE1 CE2).P X.p i
  have hP : 1 ≤ P := hS.P1 i
  obtain ⟨h1, -, h3⟩ := hD
  obtain ⟨hle, hdvd⟩ := h3 i
  have e : coarseC X.p (X.S C0 CE1 CE2) aTop b i * P = aTop i - ∑ c, b.ry i c := Nat.div_mul_cancel hdvd
  have hρ : ∑ c, b.ry i c ≤ (X.r + 1) * P := by
    calc ∑ c, b.ry i c ≤ ∑ _c : Fin (X.r + 1), P := Finset.sum_le_sum fun c _ => (h1 i c).2.le
      _ = (X.r + 1) * P := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have e2 : ((coarseC X.p (X.S C0 CE1 CE2) aTop b i : ℕ) : ℝ) * (P : ℝ) = (aTop i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, e, Nat.cast_sub hle]
  rw [e2]
  have : ((∑ c, b.ry i c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by exact_mod_cast hρ
  linarith

theorem coarseA_upper (b : SegBlock X.s X.r) (i : Fin X.s) :
    (coarseA X.p (X.S C0 CE1 CE2) b i : ℝ) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ 5 / 2 * X.L.b' := by
  have h1 : coarseA X.p (X.S C0 CE1 CE2) b i * (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).bTop i :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have h2 : ((coarseA X.p (X.S C0 CE1 CE2) b i * (X.S C0 CE1 CE2).P X.p i : ℕ) : ℝ) ≤ ((X.S C0 CE1 CE2).bTop i : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  exact h2.trans (hS.bTop i)

theorem win_ge (aTop : Fin X.s → ℕ) (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (i : Fin X.s) :
    (X.L.a : ℝ) ≤ aTop i := by
  have := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hT i)).1
  exact_mod_cast this

end Coarse

end Formalism.MainNotions.G.SymmetricFormBlocks

end
