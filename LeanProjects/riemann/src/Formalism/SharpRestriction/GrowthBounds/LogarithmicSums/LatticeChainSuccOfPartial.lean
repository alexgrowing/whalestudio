import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SecondConstantNonneg

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

theorem mul_bound {s B c R : ℝ} (hs : s ≤ B) (hc : 0 ≤ c) (hBc : B * c ≤ R) : s * c ≤ R :=
  le_trans (mul_le_mul_of_nonneg_right hs hc) hBc

theorem rpow_neg_le_inv (s : Scale) (u : ℝ) (hu : u ≤ -1) : s.x ^ u ≤ 1 / s.x := by
  have h := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le hu
  rwa [Real.rpow_neg_one, ← one_div] at h

theorem rpow_le_inv_of_le_neg_two (s : Scale) (h : 120 ≤ s.x) (u : ℝ) (hu : u ≤ -2) : s.x ^ u ≤ 1 / s.x / 120 := by
  have h1 := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le hu
  have hx := sc_x_pos s
  have h2 : s.x ^ (-2 : ℝ) = 1 / s.x / s.x := by
    rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [h2] at h1
  refine le_trans h1 ?_
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h

theorem sum_low (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    {A3 A4 PS : Finset ℕ} {badf : ℕ → ℝ} (T : Sets X K A3 A4 PS badf)
    (hZZ : WReq X K a b) (N : PrimeSumNumericFacts D L K C bo)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤
      47 / 10 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by
  have ha := sc_one_lt_a L.sc
  have hx := sc_x_pos L.sc
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
  have hA : 0 ≤ L.sc.a / L.sc.x := div_nonneg (by linarith) hx.le
  have hX'' : 0 ≤ L.sc.X'' D.R.n := by
    have := X'_le_X'' L.sc D.R.n (n_pos D); have := one_le_X' L.sc; linarith
  have hc1 := first_constant_nonneg L C hC
  have hc2 := second_constant_nonneg L C hC
  have hc3 := third_constant_nonneg L C bo hC hbo
  have hc4 := fourth_constant_nonneg K hK.1 L C hC
  have hcfl := cfl_nonneg D L.sc C hC
  refine le_trans (Finset.sum_le_sum (fun p hp =>
    low_le X K hK P C bo hC hbo h hG hSig T p (hS p hp).1 (hS p hp).2.1 (hS p hp).2.2)) ?_
  unfold E1
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  have b1 : ∑ p ∈ S, (if p ∈ prB (L.sc.X'' D.R.n + 1) then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n + 2 := by
    refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
    have := card_prB_le (L.sc.X'' D.R.n + 1) (by linarith)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have b2 : ∑ p ∈ S, (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) ≤ Real.log 4 * L.sc.p0 D.R.k :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p) (fun p _ => Real.log_natCast_nonneg p))
      (sum_log_prB _ (p0_pos D L.sc).le)
  have b3 : ∑ p ∈ S, (if p ∈ prB L.sc.X' then Real.log p else 0) ≤ Real.log 4 * L.sc.X' :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p) (fun p _ => Real.log_natCast_nonneg p))
      (sum_log_prB _ (by have := one_le_X' L.sc; linarith))
  have b4 : ∑ p ∈ S, (if p ∈ prB L.sc.X' then Real.log p / p else 0) ≤ lX L.sc :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (sum_logdiv_prB _ (one_le_X' L.sc))
  have b5 : ∑ p ∈ S, (if p ∈ A3 then Real.log p / p else 0) ≤ 1 / L.sc.x / 120 :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (le_trans T.s3 (rpow_le_inv_of_le_neg_two _ N.n5 _ (by unfold Formalism.MainNotions.G.hG; have := L.sc.eps_pos; linarith)))
  have b6 : ∑ p ∈ S, (if p ∈ A4 then Real.log p / p else 0) ≤ 1 / L.sc.x :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (le_trans T.s4 (rpow_neg_le_inv _ _ le_rfl))
  have b7 : ∑ p ∈ S, (if p ∈ PS then Real.log p / p * badf p else 0) ≤
      (D.host.TT.card : ℝ) * (1 / L.sc.x / 120) :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * badf p)
      (fun p _ => mul_nonneg (lp_nonneg p) (T.hbad0 p)))
      (le_trans T.s2 (mul_le_mul_of_nonneg_left N.n7 hN))
  have b8 : ∑ p ∈ S, (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) ≤
      1 / L.sc.x / 120 := by
    refine le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p))
      (fun p hp => mul_nonneg (lp_nonneg p)
        (add_nonneg (mul_nonneg (by norm_num) (dropI_nonneg X K a b p))
          (mul_nonneg (by norm_num) (hSig p (cand_of_mem hp)))))) ?_
    exact le_trans ((WReq_iff X K a b).1 hZZ) (rpow_le_inv_of_le_neg_two L.sc N.n5 (-9) (by norm_num))
  have q1 := mul_bound b1 (add_nonneg (mul_nonneg hM hc1) (mul_nonneg hm hcfl))
    (R := 1 / 20 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n1 hM
      have e2 := mul_le_mul_of_nonneg_left N.n1' hm
      have e3 : (D.R.m : ℝ) * (L.sc.a / L.sc.x) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := by
        have := mul_le_mul_of_nonneg_left N.one_le_card_tops (mul_nonneg hm hA)
        nlinarith
      nlinarith)
  have q2 := mul_bound b2 (mul_nonneg hM hc2)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n2 hM
      linarith)
  have q3 := mul_bound b3 (mul_nonneg hM hc3)
    (R := 3 / 2 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n3 hM
      linarith)
  have q4 := mul_bound b4 (mul_nonneg hM hc4)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n4 hM
      linarith)
  have hMa : 0 ≤ 3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a := by positivity
  have q5 := mul_bound b5 hMa
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q6 := mul_bound b6 hMa
    (R := 3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q7 := mul_bound b7 (by positivity : (0 : ℝ) ≤ 3 * (D.R.m : ℝ) * L.sc.a)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q8 := mul_bound b8 (by positivity : (0 : ℝ) ≤ 4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)
    (R := 1 / 30 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have hU : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := mul_nonneg hM hA
  linarith

theorem sum_high (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (C bo : ℝ) {a b : HH D → ℤ} (h : InWin L a b)
    (N : PrimeSumNumericFacts D L K C bo) (S : Finset ℕ) (hS : ∀ p ∈ S, L.sc.X'' D.R.n < (p : ℝ)) :
    ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤
      1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by
  obtain ⟨hS1, hS2⟩ := Sc_facts P
  obtain ⟨hth0, hth1⟩ := thS_bounds P
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
  have hX1 : 1 ≤ L.sc.X'' D.R.n := by
    have := X'_le_X'' L.sc D.R.n (n_pos D); have := one_le_X' L.sc; linarith
  obtain ⟨ht0, ht1⟩ := thW_bounds D L.sc
  have hw := sc_w''_pos L.sc D.R.n (n_pos D)
  have hl2 : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) *
      ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) := by positivity
  set R9 : Finset ℕ := Finset.Ioc ⌊L.sc.X'' D.R.n⌋₊ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ with hR9
  have hpt : ∀ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ (if p ∈ R9 then (1 : ℝ) else 0) *
      (Real.log (2 * L.sc.X'' D.R.n) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc))) := by
    intro p hp
    have hpX := hS p hp
    have hd := dfc_high P X K h p hpX
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hlt : (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L)
    · rw [if_pos hlt] at hd
      have hmem : p ∈ R9 := by
        rw [hR9]
        refine Finset.mem_Ioc.2 ⟨(Nat.floor_lt (by linarith)).2 hpX, ?_⟩
        exact_mod_cast le_trans hlt.le (Nat.le_ceil _)
      rw [if_pos hmem, one_mul]
      have h1 : max 0 (Dfc X K a b p) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc) :=
        max_le (by positivity) (by linarith)
      have h2 : Real.log p ≤ Real.log (2 * L.sc.X'' D.R.n) :=
        Real.log_le_log (by linarith) (by nlinarith)
      exact mul_le_mul h2 h1 (le_max_left _ _) hl2
    · rw [if_neg hlt] at hd
      have h1 : max 0 (Dfc X K a b p) = 0 := max_eq_left (by linarith)
      rw [h1, mul_zero]
      split_ifs
      · rw [one_mul]; exact hcoef
      · rw [zero_mul]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [← Finset.sum_mul]
  have b9 : ∑ p ∈ S, (if p ∈ R9 then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n * thS L + 2 := by
    refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hR9, Nat.card_Ioc]
    have hle : ⌊L.sc.X'' D.R.n⌋₊ ≤ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ :=
      le_trans (Nat.floor_le_floor (by nlinarith)) (Nat.floor_le_ceil _)
    rw [Nat.cast_sub hle]
    have h1 := Nat.ceil_lt_add_one (mul_nonneg (by linarith) (by linarith) : 0 ≤ L.sc.X'' D.R.n * (1 + thS L))
    have h2 := Nat.lt_floor_add_one (L.sc.X'' D.R.n)
    linarith
  refine mul_bound b9 hcoef ?_
  have e1 := mul_le_mul_of_nonneg_left N.n9 hM
  linarith

theorem inWin_of_box {K : Consts} {a b : HH D → ℤ} (ha : a ∈ box D (winA D L.sc)) (hb : b ∈ box D (winB D K L.sc)) :
    InWin L a b := by
  classical
  intro t ht
  unfold box at ha hb
  have h1 := Fintype.mem_piFinset.1 ha t
  have h2 := Fintype.mem_piFinset.1 hb t
  rw [if_pos ht] at h1 h2
  unfold winA at h1
  unfold winB at h2
  obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.1 h1
  obtain ⟨h2a, _⟩ := Finset.mem_Icc.1 h2
  exact ⟨Int.ceil_le.1 h1a, Int.le_floor.1 h1b, Int.ceil_le.1 h2a⟩

theorem latticeChain_succ_of_partial (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    (hG : GainBoundAll X K C bo) (hSig0 : ∀ a b p, Cand D L K p → 0 ≤ Sig X K a b p) (h2 : adm2 D L X) (h3 : adm3 D L)
    (h4 : ArchimedeanSignatureMatching D L K) (N : PrimeSumNumericFacts D L K C bo) : PointsLemma D L X K := by
  classical
  intro a ha b hb hZZ
  have hW := inWin_of_box ha hb
  have hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p := fun p hp => hSig0 a b p hp
  have hXX := X'_le_X'' L.sc D.R.n (n_pos D)
  have h2' := h2.2
  unfold BTT at h2'
  unfold adm3 at h3
  have h4' := h4.2.2.2.2
  have T : Sets X K _ _ _ (fun p => ((D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t))).card : ℝ)) :=
    { hA3 := fun p hp hc hX ho => Finset.mem_filter.2 ⟨by
          unfold primesResidueBelow
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 (by linarith)), hp, by linarith, hc⟩, ho⟩
      hA4 := fun p hp hX hB => Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 hX), hp, hB⟩
      hPS := fun p hC => Finset.mem_filter.2 ⟨by
          unfold primesResidueBelow
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 hC.2.1), hC.1, hC.2.1, hC.2.2.1⟩, hC.2.2.2.1⟩
      hPSsub := fun p hp => by
          have h1 := (Finset.mem_filter.1 hp).1
          unfold primesResidueBelow at h1
          have h2 := (Finset.mem_filter.1 h1).2
          exact mem_prB.2 ⟨h2.1, h2.2.1⟩
      hbad := fun p _ => by
          have : (D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)) ⊆
              D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t)) := by
            intro t ht
            obtain ⟨ht1, ht2⟩ := Finset.mem_sdiff.1 ht
            refine Finset.mem_filter.2 ⟨ht1, fun hg => ht2 (Finset.mem_filter.2 ⟨ht1, ?_⟩)⟩
            unfold goodReps reps
            exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hg⟩
          exact_mod_cast Finset.card_le_card this
      hbad0 := fun p => Nat.cast_nonneg _
      s3 := h3
      s4 := h4'
      s2 := h2' }
  refine ⟨?_, ?_⟩
  · intro S hS
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ L.sc.X'' D.R.n)
      (fun p : ℕ => Real.log p * max 0 (Dfc X K a b p))
    have l1 := sum_low X K hK P C bo hC hbo hW (hG a b hW) hSig T hZZ N
      (S.filter (fun p : ℕ => (p : ℝ) ≤ L.sc.X'' D.R.n))
      (fun p hp => ⟨(hS p (Finset.mem_filter.1 hp).1).1, (hS p (Finset.mem_filter.1 hp).1).2, (Finset.mem_filter.1 hp).2⟩)
    have l2 := sum_high P X K C bo hW N (S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ L.sc.X'' D.R.n))
      (fun p hp => not_le.1 (Finset.mem_filter.1 hp).2)
    have hMA : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := by
      have := sc_one_lt_a L.sc
      have := sc_x_pos L.sc
      positivity
    have e : 5 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / L.sc.x =
        5 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by ring
    rw [e]
    change ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ _
    linarith
  · intro S _
    have hMa : 0 ≤ ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a := by
      have := sc_one_lt_a L.sc
      positivity
    refine le_trans (Finset.sum_le_sum (fun p _ => io_le X K hK P hW hSig p)) ?_
    rw [← Finset.sum_mul]
    have b8 : ∑ p ∈ S, (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) ≤
        L.sc.x ^ (-9 : ℝ) := by
      refine le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p))
        (fun p hp => mul_nonneg (lp_nonneg p)
          (add_nonneg (mul_nonneg (by norm_num) (dropI_nonneg X K a b p))
            (mul_nonneg (by norm_num) (hSig p (cand_of_mem hp)))))) ?_
      exact (WReq_iff X K a b).1 hZZ
    exact mul_bound b8 hMa (le_of_eq (by ring))

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
