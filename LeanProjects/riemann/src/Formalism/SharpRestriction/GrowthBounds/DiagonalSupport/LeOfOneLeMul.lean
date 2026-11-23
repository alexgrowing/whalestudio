import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundJoint

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Small

theorem le_sq_of_one_le (x : ℝ) (h : 1 ≤ x) : x ≤ x ^ 2 := by nlinarith

theorem two_mul_le_sq (a : ℝ) (h : 2 ≤ a) : 2 * a ≤ a ^ 2 := by nlinarith

theorem le_of_one_le_mul (l d t : ℝ) (hl : 1 ≤ l) (hd : 0 ≤ d) (h : l * d ≤ t) : d ≤ t := by nlinarith

theorem kap_fin (N k ℓ : ℝ) (hN : 0 ≤ N) (hk : 1 ≤ k) (hℓ : 0 ≤ ℓ) : N * (k * (2 * ℓ)) ≤ 20 * (N * k ^ 2 * ℓ) := by
  have h1 := le_sq_of_one_le k hk
  have h2 : 0 ≤ N * ℓ := mul_nonneg hN hℓ
  have h3 : (N * ℓ) * k ≤ (N * ℓ) * k ^ 2 := mul_le_mul_of_nonneg_left h1 h2
  have h4 : 0 ≤ (N * ℓ) * k ^ 2 := mul_nonneg h2 (by positivity)
  nlinarith

end Small

structure NB (p m r N : ℕ) (a : ℝ) : Prop where
  two_le_a : 2 ≤ a
  p_le : (p : ℝ) ≤ a
  fourN : 4 * (N : ℝ) ≤ a
  r_le : (r : ℝ) ≤ a
  one_le_log : 1 ≤ Real.logb p a
  one_le_Lg : 1 ≤ (N : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a

theorem nb_of {C : ℝ} (hC1 : 1 ≤ C) {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) : NB p m r TT.card a := by
  have hB := hyps_basic hC1 H
  obtain ⟨h1, h2, _, _, _, _, _, _, _, _, h11, h12⟩ := H
  have hr1 : 1 ≤ r := by omega
  have ha2 := hB.two_le_a
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp1' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hk7 : (7 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have := hB.m_ge
    exact_mod_cast (by omega : 7 ≤ m + 1)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hG1 : goodG' r de h x ≠ 0 := by
    have := hB.one_le_depth_alt
    have := hB.depth_le_good_exponent
    omega
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1
  have hcc : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
    have h8' : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
    have : (0 : ℝ) ≤ (r : ℝ) * TT.card * c0 + 2 * r * n' * cpp := by positivity
    linarith
  obtain ⟨z1, z2, z3⟩ := factor_le_product_seven C (((m + 1 : ℕ) : ℝ) ^ 3) ((r : ℝ) ^ 2) (TT.card : ℝ)
    (((p : ℝ) ^ goodG' r de h x) ^ 5) ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) Y hC1
    (one_le_pow₀ hk1) (one_le_pow₀ hrr) hN1 (one_le_pow₀ hQ1) hcc (by linarith [hB.two_le_Y])
  have z1' := le_trans z1 h12
  have z2' := le_trans z2 h12
  have z3' := le_trans z3 h12
  clear z1 z2 z3 h12
  have h4N : 4 * (TT.card : ℝ) ≤ a := by
    have e : (7 : ℝ) ^ 3 ≤ ((m + 1 : ℕ) : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hk7 3
    have : 4 * (TT.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 3 * (TT.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hra : (r : ℝ) ≤ a := le_trans (le_sq_of_one_le _ hrr) z2'
  have hpa : (p : ℝ) ≤ a := by
    have e1 : (p : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := le_self_pow₀ hp1 hG1
    have e2 : (p : ℝ) ^ goodG' r de h x ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 := le_self_pow₀ hQ1 (by norm_num)
    linarith
  have hℓ1 : (1 : ℝ) ≤ Real.logb p a := by
    have := Real.logb_le_logb_of_le hp1' (by linarith) hpa
    rwa [Real.logb_self_eq_one hp1'] at this
  exact ⟨ha2, hpa, h4N, hra, hℓ1,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hk1)) hℓ1⟩

theorem kapFl_le {p n' m : ℕ} (hp : 2 ≤ p) {TT : Finset (Fin n')} {lam0 : Fin n' → Fin (m + 1) → ℤ} {a : ℝ}
    (ha2 : 2 ≤ a) (hℓ1 : 1 ≤ Real.logb p a)
    (hfd : ∀ s ∈ TT, a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a) :
    (kapFl p (m + 1) (dT TT lam0) : ℝ) ≤ 20 * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) := by
  have hp1' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  unfold kapFl
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul]
  have hoff : ∀ s : Fin n', s ∈ (Finset.univ : Finset (Fin n')) → s ∉ TT →
      ((m + 1 : ℕ) : ℝ) * ((Nat.log p (dT TT lam0 s) : ℕ) : ℝ) = 0 := by
    intro s _ hs
    have e : dT TT lam0 s = 0 := by unfold dT; rw [if_neg hs]
    rw [e]
    simp
  have hon : ∀ s ∈ TT, ((m + 1 : ℕ) : ℝ) * ((Nat.log p (dT TT lam0 s) : ℕ) : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) * (2 * Real.logb p a) := by
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have e : dT TT lam0 s = flatDeg lam0 s := by unfold dT; rw [if_pos hs]
    rw [e]
    obtain ⟨b1, b2⟩ := hfd s hs
    have l1 : ((Nat.log p (flatDeg lam0 s) : ℕ) : ℝ) ≤ Real.logb p (flatDeg lam0 s : ℝ) :=
      Real.natLog_le_logb _ _
    have l2 : Real.logb p (flatDeg lam0 s : ℝ) ≤ Real.logb p (a ^ 2) :=
      Real.logb_le_logb_of_le hp1' (by linarith) (le_trans b2 (two_mul_le_sq a ha2))
    have l3 : Real.logb p (a ^ 2) = 2 * Real.logb p a := by rw [Real.logb_pow]; norm_num
    linarith
  rw [← Finset.sum_subset (Finset.subset_univ TT) hoff]
  have hs1 := Finset.sum_le_card_nsmul TT _ _ hon
  rw [nsmul_eq_mul] at hs1
  exact le_trans hs1 (kap_fin _ _ _ (Nat.cast_nonneg _) hk1 (by linarith))

section At

variable {p n' m r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r}
  {lam0 : Fin n' → Fin (m + 1) → ℤ} {a Y : ℝ} {cP : ℕ}

theorem numAt_of (hk : m + 1 = r + K) (hF : FramesOK TT L₁ L₂ N₁ G' F) (hp : 3 ≤ p) (hr : 2 ≤ r) (hL : L₁ ≤ L₂)
    (hnb : NB p m r TT.card a)
    (hfd : ∀ s ∈ TT, a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a)
    (hcP : 80 * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) < (cP : ℝ))
    (hII5 : ∀ (Dd : ℕ) (Qj dj B : ℝ), (p : ℝ) ^ Dd ≤ Formalism.CountingSumsFrames.QII p G' → 1 ≤ Qj → Qj ≤ Formalism.CountingSumsFrames.QII p G' →
      dj ≤ 3 * a * (p : ℝ) ^ (-(Dd : ℤ) - L₁ - 1) → a / ((p : ℝ) ^ Dd * Qj) ≤ B →
      r * dj / Qj ≤ 3 * r * (p : ℝ) ^ (-(L₁ : ℤ) - 1) * B ∧
        3 * r * (p : ℝ) ^ (-(L₁ : ℤ) - 1) * B ≤ Formalism.CountingSumsFrames.slII Y (r + K) B / 8)
    (hII0 : ∀ B : ℝ, a / Formalism.CountingSumsFrames.QII p G' ≤ B → 100 * (r : ℝ) ^ 2 * (cP : ℝ) ≤ Formalism.CountingSumsFrames.slII Y (r + K) B) :
    NumAt (K := K) p O F (flatDeg lam0) Y N₁ G' cP (dT TT lam0) 20
      ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) := by
  have hV := hF.2.1
  have hr1 : 1 ≤ r := by omega
  have ha0 : 0 ≤ a := by linarith [hnb.two_le_a]
  intro J _ Dt dPl dNo ka rho hT hBk
  obtain ⟨hTd, hc, hsl⟩ := hT
  have hJ := hTd.1
  have hnL := hTd.2.1
  have hdd : Dt.d = dPl := hTd.2.2.2.1
  have hnch := hTd.2.2.2.2.2.1
  have hd : ∀ x, (lowP F p x : ℝ) * (Dt.d x : ℝ) ≤ 2 * a := by
    intro x
    have htop : posOf n' (posTL F x) ∈ TT := by
      have := (posTL_seg F hV hr1 hnL x).2.2
      rwa [hF.1] at this
    have e := hBk.2 x
    have e2 : dT TT lam0 (posOf n' (posTL F x)) = flatDeg lam0 (posOf n' (posTL F x)) := by
      unfold dT; rw [if_pos htop]
    rw [e2] at e
    have e3 : lowP F p x * Dt.d x ≤ flatDeg lam0 (posOf n' (posTL F x)) := by
      rw [hdd]
      have := Nat.mul_le_mul_left (lowP F p x) (Nat.le_add_right (dPl x) (dNo x))
      omega
    have e4 : ((lowP F p x * Dt.d x : ℕ) : ℝ) ≤ (flatDeg lam0 (posOf n' (posTL F x)) : ℝ) := by exact_mod_cast e3
    have := (hfd _ htop).2
    push_cast at e4
    linarith
  have hd2 : ∀ x, (Dt.d x : ℝ) ≤ 2 * a := by
    intro x
    have hl : (1 : ℝ) ≤ (lowP F p x : ℝ) := by
      have : 1 ≤ lowP F p x := Nat.one_le_pow _ _ (by omega)
      exact_mod_cast this
    exact le_of_one_le_mul _ _ _ hl (Nat.cast_nonneg _) (hd x)
  have hcard : Fintype.card (TL J Dt.nL r) ≤ TT.card := by
    have := card_TL_le F hV hr1 hJ hnL
    rwa [hF.1] at this
  obtain ⟨s1, s2⟩ := sizes_le Dt TT.card (m + 1) a (by omega) hr1 (by omega) hcard hnch hd2 hnb.two_le_a hnb.p_le
    hnb.fourN hnb.r_le
  refine ⟨?_, ?_, s1, s2⟩
  · refine slack_bound_joint hF hr hp hL (flatDeg lam0) Y (r + K) _ K Dt dPl ka hTd (cP : ℝ) hc (Nat.cast_nonneg _) hsl a ha0 ?_ hd
      hII5 hII0
    intro s hs
    rw [hF.1] at hs
    exact (hfd s hs).1
  · rw [hc]
    linarith

end At

theorem numStep_of : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, NumStep C 20 CLa := by
  obtain ⟨C0, hC0, H0⟩ := Formalism.CountingSumsFrames.Top.paramsII0 1 1 le_rfl le_rfl
  obtain ⟨C5, hC5, H5⟩ := Formalism.CountingSumsFrames.Top.paramsII5 1 1 le_rfl le_rfl
  refine ⟨max (max C0 C5) 10, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro C hC CLa p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  obtain ⟨_, H, hF, _, _, _⟩ := hD
  have hC0' : C0 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hC5' : C5 ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hC10 : 10 ≤ C := le_trans (le_max_right _ _) hC
  have hC1 : 1 ≤ C := by linarith
  have hB := hyps_basic hC1 H
  have hnb := nb_of hC1 H
  have cg0 := counting_hypotheses_of_hyps hC0 (hyps_mono hC0 hC0' H) 0 (Nat.zero_le _) (Nat.zero_le _)
  have cg5 := counting_hypotheses_of_hyps hC5 (hyps_mono hC5 hC5' H) 0 (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨h1, h2, h3, _, h5, _, _, _, _, h10, h11, _⟩ := H
  have ha0 : 0 ≤ a := by linarith [hnb.two_le_a]
  have hfd := fun s hs => flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 s hs
  have hcPe : ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) = Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar := by
    unfold cPrime Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII
    push_cast
    ring
  have hcS : (cStar : ℝ) ≤ ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) := by
    have : cStar ≤ cPrime n' r TT.card c0 cpp cStar := by unfold cPrime; omega
    exact_mod_cast this
  have h11' : 8 * ((Dp : ℝ) + 1) ≤ (cStar : ℝ) := by exact_mod_cast h11
  have hcP : 80 * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) <
      ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) := by
    have e : C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a =
        C * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) := by ring
    have e2 : 10 * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) ≤
        C * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) :=
      mul_le_mul_of_nonneg_right hC10 (by linarith [hnb.one_le_Lg])
    linarith
  rw [hk] at cg0 cg5
  have A5 := (H5 p r TT.card (orbitWindowCount r de h x) 0 1 (r + K) n' L₁ (goodG' r de h x) Y a c0 cpp Dp cStar cg5).2.1
  have A0 := (H0 p r TT.card (orbitWindowCount r de h x) 0 1 (r + K) n' L₁ (goodG' r de h x) Y a 0 c0 cpp Dp cStar cg0
    le_rfl (by unfold Formalism.CountingSumsFrames.QII; positivity)).2.1
  refine ⟨hnb.one_le_Lg, kapFl_le (by omega) hnb.two_le_a hnb.one_le_log hfd, ?_⟩
  refine numAt_of hk hF (by omega) h2 (by have := h3.2.1; omega) hnb hfd hcP A5 ?_
  intro Bb hBb
  have q := (A0 Bb hBb).1
  rw [hcPe]
  have n1 : 0 ≤ 24 * (((orbitWindowCount r de h x : ℕ) : ℝ) + r) * c0 := by positivity
  have n2 : 0 ≤ Formalism.CountingSumsFrames.mStarII (orbitWindowCount r de h x) (r + K) (Formalism.CountingSumsFrames.QII p (goodG' r de h x))
      (Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar) 0 := by
    unfold Formalism.CountingSumsFrames.mStarII Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII Formalism.CountingSumsFrames.QII
    positivity
  linarith

theorem restNum (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestNum D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨C₁, h1, h2⟩ := numStep_of
  exact ⟨20, C₁, by norm_num, h1, fun C hC => h2 C hC CLa⟩

end Formalism.MainNotions.Proposition5Numerics
