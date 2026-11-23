import CompanionTheory.AutomorphicTheory.BesselWaveGrids.CoefOfOfWsp

noncomputable section

namespace CompanionTheory.WaveGrid.WEnd

open MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants CompanionTheory.WaveGrid CompanionTheory.WaveGrid.SpanBall
open CompanionTheory.WaveGrid.Coef CompanionTheory.WaveGrid.WAt
open CompanionTheory.WaveGrid.MomL (mnr momL)
open CompanionTheory.LimBd.Main (ZuckT ZuckDualT Wsp Box gap_of_box)
open scoped ENNReal

def gapY (k r : ℕ) : ℝ :=
  ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)

theorem pow_four_le_rpow_nine_halves (r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)) (by norm_num)

theorem thrX_le_gapY (k r : ℕ) : thrX k r ≤ gapY k r := by
  unfold thrX gapY
  have h1 : ((r : ℝ) + 1) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) 4
  have e : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (h1.trans (pow_four_le_rpow_nine_halves r)) (by positivity)

theorem mul_le_gapY (k r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  mul_le_mul (pow_four_le_rpow_nine_halves r) (le_add_of_nonneg_left (by positivity)) (by positivity) (by positivity)

theorem fourth_power_le_gap (k r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ gapY k r :=
  le_trans (le_mul_of_one_le_right (by positivity)
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)))) (mul_le_gapY k r)

theorem cube_le_gap (k r : ℕ) : ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  le_trans (le_mul_of_one_le_left (by positivity)
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)))) (mul_le_gapY k r)

theorem num_of {k r : ℕ} (hk : 1 ≤ k) {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    (hlam : IsHCParam lam) (hu : HypType k r lam u b)
    (hc : ∀ a : Fin (2 * r + k + 1), a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8)
    (hn : ∀ a : Fin (2 * r + k + 1), k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv) (hb : ∀ a, |lam a| ≤ b)
    (hg : ∀ a c, a < c → ga ≤ lam a - lam c) (hh : GapAtLeast (PI.BesselPeriodGGP.eps48 k r) lam h)
    (hok : ThreeDimData.GapOK k r (h / 4)) (h1 : 100 * ((q0 : ℝ) + 1) ≤ ga) (h2 : 100 * ((q0 : ℝ) + 1) ≤ h)
    (h3 : 10 ^ 6 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv) : BranchingSupport.Num k r lam u b bv ga h q0 := by
  refine ⟨hk, hlam, fun a i hi => ?_, fun a ha => ?_, fun a ha => ?_, hc, hn, hb,
    fun i hi => hu.u_le i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2, fun a c hac _ => hg a c hac,
    hh, hok, h1, h2, h3⟩
  · obtain ⟨m1, e1⟩ := hlam.2 a
    obtain ⟨m2, e2⟩ := hu.half i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2
    refine ⟨m1 - m2 + r, ?_⟩
    push_cast at e1 ⊢
    linarith
  · exact (hu.inter.2 (a.cast (by ring))).1 (by simpa using ha)
  · exact (hu.inter.2 (a.cast (by ring))).2 (show a.val + 2 ≤ k by omega)

theorem bp_max {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {b C C' : ℝ} {n₀ p₀ A : ℕ} (hb : 1 ≤ b) (hC : C ≤ C')
    (hA : 2 * p₀ + n₀ ≤ A) (h : TBB.ThmBpAt p f b C n₀ p₀) (γ : Formalism.FourierDecayAlt.C.LPt) (hγ : D.IsLocPt γ (P.r + 1))
    (hG : 0 < TBB.Gp p γ) : ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤
      ENNReal.ofReal (b ^ (C' * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * max 1 (1 / TBB.Gp p γ) ^ A) * TBB.jN2 p f := by
  refine (h γ hγ hG).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hC (by positivity))) ?_
    (pow_nonneg (inv_nonneg.2 hG.le) _) (Real.rpow_nonneg (by linarith) _)
  exact (pow_le_pow_left₀ (inv_nonneg.2 hG.le) (by rw [one_div]; exact le_max_right _ _) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) hA)

def In91 : Prop :=
  (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : BranchingSupport.Rep k r),
    BranchingSupport.Num k r lam u b bv ga h q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 k r) lam → ∃ R, BranchingSupport.IsFam lam q0 R) ∧
  ∀ C : ℝ, 0 ≤ C → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ),
    BranchingSupport.Num P.k P.r lam P.u b bv ga h q0 → BranchingSupport.Num P.k P.r lam P.u' b bv ga h q0 →
    P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) →
    ∀ (a : ℕ) (R0 : BranchingSupport.Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), BallW.CoefOf R0 f →
    (∀ ν₀ : Fin (2 * P.r + P.k + 1) → ℤ, BranchingSupport.n1 ν₀ + (P.r + 1) * a + (P.r + 1) * (P.r + 2) ≤ q0 →
      R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun s => lam s + (ν₀ s : ℝ)) → BigCellDerivativeExpansion p f b (C / 2 + 6) a) ∧
    ∀ (j : ℕ) (hj : j ≤ P.r), (P.r + 1) * a + (P.r + 1) * (P.r + 2) ≤ q0 →
      R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) lam →
      momL p f hj a ≤ ENNReal.ofReal (b ^ ((C + 12) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * a)) * TBB.jN2 p f

def WBp (Cb : ℝ) : Prop :=
  ∀ C Ca : ℝ, 0 ≤ C → ∃ C₅ Cg₀ : ℝ, 0 ≤ C₅ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] [CompleteSpace Wp] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv : ℝ) (j : ℕ) (hj : j ≤ P.r) (a : ℕ),
    KFinDSCoef (PI.BesselPeriodGGP.eps48 P.k P.r) lam f → HypType P.k P.r lam P.u b → HypType P.k P.r lam P.u' b →
    (∀ s : Fin (2 * P.r + P.k + 1), s.val + 1 < P.k → 0 ≤ lam s ∧ lam s ≤ bv / 8) →
    (∀ s : Fin (2 * P.r + P.k + 1), P.k ≤ s.val + 1 → -2 * bv ≤ lam s ∧ lam s ≤ -bv) → (∀ s, |lam s| ≤ b) →
    Cg * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv →
    (∀ s s', s < s' → Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4 ≤ lam s - lam s') →
    GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) lam (Cg * gapY P.k P.r) → ThreeDimData.GapOK P.k P.r (Cg * gapY P.k P.r / 4) →
    1 ≤ P.T → 1 ≤ P.T' → P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) →
    ((30 * ((P.r : ℝ) + 1) ^ 2 + 6 ≤ |P.u p.l0 - P.u' p.l0| ∧ KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) ∨
      (P.u = P.u' ∧ ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (30 * ((P.r : ℝ) + 1) ^ 2 + 6) + 1 ≤ P.u l - P.u (l + 1))) →
    (a : ℝ) ≤ Ca * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 →
    ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      ENNReal.ofReal (‖mnr hj γ‖ ^ (2 * a) * TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤
        ENNReal.ofReal (b ^ (C₅ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 5) * max 1 (1 / TBB.Gp p γ) ^ (40 * (P.r + 1) ^ 2)) *
          TBB.jN2 p f

set_option maxHeartbeats 1600000 in
theorem wBp_of {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct : ℝ} (hCt : 0 ≤ Ct)
    (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3) (hZ : ZuckT t) (hZd : ZuckDualT t) (hS : LimSteps)
    (hD : EndDiffW t) (hQ : EndEqW t) (hK : PI.KFinSmooth) (H : In91) (hU : UniqG) (Cb : ℝ) : WBp Cb := by
  intro C Ca hC
  have hC3 : 0 ≤ C / 2 + 6 := by positivity
  obtain ⟨C₁, CA₁, H1⟩ := hD Cb _ 0 1 hC3 le_rfl (by norm_num)
  obtain ⟨C₂, CA₂, H2⟩ := hQ _ 0 1 hC3 le_rfl (by norm_num)
  obtain ⟨c₃, HW⟩ := weighted
  have a1 := abs_nonneg CA₁
  have a2 := abs_nonneg CA₂
  have a3 := abs_nonneg c₃
  have a4 := abs_nonneg Ca
  have a5 : 0 ≤ max (max C₁ C₂) 0 := le_max_right _ _
  refine ⟨4 * |Ca| + max (max C₁ C₂) 0 + (C + 12) * |Ca|, 10 ^ 6 + Ct + |CA₁| + |CA₂| + |c₃| + 100 * |Ca|,
    by positivity, ?_⟩
  intro Cg hCg P Wp Wq _ _ _ _ _ _ _ p f lam b bv j hj a hf hTy hTy' hcl hnd hlamb hbv hg4 hgap hok hT1 hT1' hT hT'
    hcase ha γ hγ hG
  have hk2 : 2 ≤ P.k := p.hl.2.2
  have hlam : IsHCParam lam := by
    obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hf
    exact h
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hkR : (2 : ℝ) ≤ P.k := by exact_mod_cast hk2
  have hY1 := thrX_le_gapY P.k P.r
  have hY2 := fourth_power_le_gap P.k P.r
  have hY3 := cube_le_gap P.k P.r
  have hX0 := thrX_nonneg P.k P.r
  have htn := ht (2 * P.r + P.k + 1) (PI.BesselPeriodGGP.eps48 P.k P.r) (by omega)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((2 * P.r + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((2 * P.r + P.k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (((P.r + 1) * a : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = gapY P.k P.r := ⟨_, rfl⟩
  have hm' : m = 2 * ((P.r : ℝ) + 1) := by rw [hm]; push_cast; ring
  have hn' : n = 2 * (P.r : ℝ) + P.k + 1 := by rw [hn]; push_cast; ring
  have hm2 : 2 ≤ m := by linarith
  have hmn : m ≤ n := by linarith
  have hm3 : 8 ≤ m ^ 3 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hm2 3)
  have hm34 : m ^ 3 ≤ m ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hm45 : m ^ 4 ≤ m ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hn7 : m ^ 4 ≤ n ^ 7 :=
    (pow_le_pow_left₀ (by linarith) hmn 4).trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  have hn17 : n ≤ n ^ 7 := le_self_pow₀ (by linarith) (by norm_num)
  have hbvb : bv ≤ b := by
    have h1 := (hnd ⟨P.k, by omega⟩ (by simp)).2
    have h2 := (abs_le.1 (hlamb ⟨P.k, by omega⟩)).1
    linarith
  rw [← hm] at hY2 hg4 ha
  rw [← hn] at hY3 htn hbv
  rw [← hY] at hY1 hY2 hY3 hgap hok
  have ha' : (a : ℝ) ≤ |Ca| * m ^ 3 := ha.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  have he0 : 0 ≤ e := he ▸ Nat.cast_nonneg _
  have hem : e ≤ |Ca| * m ^ 4 := by
    rw [he]
    push_cast
    calc ((P.r : ℝ) + 1) * a ≤ m * (|Ca| * m ^ 3) := mul_le_mul (by linarith) ha' (Nat.cast_nonneg _) (by linarith)
      _ = _ := by ring
  have hCg6 : (10 : ℝ) ^ 6 ≤ Cg := by linarith
  have hCn : Cg * m ^ 4 ≤ b := (mul_le_mul_of_nonneg_left hn7 (by linarith)).trans (hbv.trans hbvb)
  have hCn' : 10 ^ 6 * n ^ 7 ≤ bv := (mul_le_mul_of_nonneg_right hCg6 (by linarith)).trans hbv
  have hcm : (10 ^ 6 + 100 * |Ca|) * m ^ 4 ≤ Cg * m ^ 4 := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hCam : 0 ≤ |Ca| * m ^ 4 := mul_nonneg a4 (by linarith)
  have hL : HypLam P.k P.r lam ((|Ca| + 5) * m ^ 4) (Cg * m ^ 4) b :=
    { hc := hlam
      lam_le := hlamb
      c_ge := by linarith
      b_ge_three := by linarith
      b_ge_k := by
        have := mul_le_mul_of_nonneg_right Real.exp_one_lt_d9.le (Nat.cast_nonneg P.k : (0 : ℝ) ≤ P.k)
        linarith only [this, hn', hr, hkR, hn17, hCn', hbvb]
      b_ge_c := by linarith
      g_ge := by linarith
      gap := fun s s' hs => by
        have := hg4 s s' (by rw [Fin.lt_def]; omega)
        linarith }
  have hb3 := hL.b_ge_three
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hnb : n ≤ b := by linarith
  have hYall : (10 ^ 6 + Ct + |CA₁| + |CA₂| + |c₃| + 100 * |Ca|) * Y ≤ Cg * Y :=
    mul_le_mul_of_nonneg_right hCg (by linarith)
  have htY : t _ (PI.BesselPeriodGGP.eps48 P.k P.r) ≤ Ct * Y := htn.trans (mul_le_mul_of_nonneg_left hY3 hCt)
  have heY : e ≤ |Ca| * Y := hem.trans (mul_le_mul_of_nonneg_left hY2 a4)
  have p1 : 0 ≤ Ct * Y := mul_nonneg hCt (by linarith)
  have p2 : 0 ≤ |CA₁| * Y := mul_nonneg a1 (by linarith)
  have p3 : 0 ≤ |CA₂| * Y := mul_nonneg a2 (by linarith)
  have p4 : 0 ≤ |c₃| * Y := mul_nonneg a3 (by linarith)
  have p5 : 0 ≤ |Ca| * Y := mul_nonneg a4 (by linarith)
  have q1 : CA₁ * thrX P.k P.r ≤ |CA₁| * Y := mul_le_mul (le_abs_self _) hY1 hX0 a1
  have q2 : CA₂ * thrX P.k P.r ≤ |CA₂| * Y := mul_le_mul (le_abs_self _) hY1 hX0 a2
  have q3 : (|c₃| + 46) * thrX P.k P.r ≤ (|c₃| + 46) * Y := mul_le_mul_of_nonneg_left hY1 (by linarith)
  set q0 : ℕ := (P.r + 1) * a + (P.r + 1) * (40 * (P.r + 1) ^ 2) + (P.r + 1) * (P.r + 2) with hq0
  have hq : 100 * ((q0 : ℝ) + 1) ≤ Cg * m ^ 4 := by
    have e2 : ((P.r : ℝ) + 1) * (40 * ((P.r : ℝ) + 1) ^ 2) = 5 * m ^ 3 := by rw [hm']; ring
    have e3 : ((P.r : ℝ) + 1) * (P.r + 2) ≤ m ^ 3 := by
      rw [hm']
      nlinarith only [hr, mul_nonneg hr hr, mul_nonneg hr (mul_nonneg hr hr)]
    have e4 : (q0 : ℝ) = e + ((P.r : ℝ) + 1) * (40 * ((P.r : ℝ) + 1) ^ 2) + ((P.r : ℝ) + 1) * (P.r + 2) := by
      rw [hq0, he]; push_cast; ring
    rw [e4]
    linarith
  have hq' : Cg * m ^ 4 ≤ Cg * Y := mul_le_mul_of_nonneg_left hY2 (by linarith)
  have hN := num_of (by omega) hlam hTy hcl hnd hlamb hg4 hgap hok hq (hq.trans hq') (hn ▸ hCn')
  have hN' := num_of (by omega) hlam hTy' hcl hnd hlamb hg4 hgap hok hq (hq.trans hq') (hn ▸ hCn')
  obtain ⟨R, hfam⟩ : ∃ R : (Fin (2 * P.r + P.k + 1) → ℤ) → BranchingSupport.Rep P.k P.r, BranchingSupport.IsFam lam q0 R := by
    obtain ⟨H₀, i1, i2, i3, σ, -, -, h1, h2, -⟩ := hf
    exact H.1 P.k P.r lam P.u b bv _ _ q0 { H := H₀, σ := σ } hN ⟨h1, h2⟩
  have H91 := H.2 C hC P Wp Wq p lam b bv _ _ q0 hN hN' hT hT'
  have g1 : n ^ 3 + 1 < Cg * Y - 2 * e := by linarith only [hYall, heY, p1, p2, p3, p4, p5, hY2, hY3, hm3, hm34]
  have g2 : ∀ x d : ℝ, x ≤ |CA₁| * Y + |CA₂| * Y → d ≤ 5 * m ^ 3 →
      t _ (PI.BesselPeriodGGP.eps48 P.k P.r) + x + 3 * d + 1 < Cg * Y - 2 * e := fun x d hx hd => by
    linarith only [hx, hd, htY, hYall, heY, p4, p5, hY2, hm3, hm34]
  have g3 : ∀ d : ℝ, d ≤ 5 * m ^ 3 → e + d ≤ (|Ca| + 5) * m ^ 4 := fun d hd => by linarith only [hd, hem, hm34]
  have g4 : t _ (PI.BesselPeriodGGP.eps48 P.k P.r) + (|c₃| + 46) * thrX P.k P.r + 3 * e + 1 < Cg * Y := by
    linarith only [q3, htY, hYall, heY, p2, p3, p5, hY2, hm3, hm34]
  have g5 : 0 ≤ (|c₃| + 46) * thrX P.k P.r := mul_nonneg (by linarith only [a3]) hX0
  have hTT : b ^ (-(0 * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T' := by
    rw [zero_mul, neg_zero, Real.rpow_zero]
    exact one_le_mul_of_one_le_of_one_le hT1 hT1'
  have hTq : 1 ≤ TBB.Tq p := by
    unfold TBB.Tq
    rw [p.hP.2.2.2.2.1]
    exact hT1'
  have hp₀ : (((2 * (P.r + 1) : ℕ) : ℕ) : ℝ) ≤ 1 * (3 * ((P.r : ℝ) + 1)) + 1 := by push_cast; linarith
  have hd1 : (((2 * P.r + 2) * (2 * (P.r + 1)) : ℕ) : ℝ) ≤ 5 * m ^ 3 := by
    rw [hm']
    push_cast
    nlinarith only [hr, mul_nonneg hr hr, mul_nonneg hr (mul_nonneg hr hr)]
  have hd2 : (((2 * P.r + 2) * (2 * (P.r + 1)) + (30 * (P.r + 1) ^ 2 + 6) * (P.r + 1) : ℕ) : ℝ) ≤ 5 * m ^ 3 := by
    rw [hm']
    push_cast
    nlinarith only [hr, mul_nonneg hr hr, mul_nonneg hr (mul_nonneg hr hr)]
  have hB : ∀ ν ∈ ball _ ((P.r + 1) * a),
      ∀ F ∈ Wsp P.k P.r Wp Wq (PI.BesselPeriodGGP.eps48 P.k P.r) (fun s => lam s + (ν s : ℝ)),
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ) ≤
        ENNReal.ofReal (b ^ (max (max C₁ C₂) 0 * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) *
          max 1 (1 / TBB.Gp p γ) ^ (40 * (P.r + 1) ^ 2)) * TBB.jN2 p F := by
    intro ν hν F hF
    have hν1 : BranchingSupport.n1 ν ≤ (P.r + 1) * a := sum_natAbs_le_of_mem_ball _ ν hν
    have hbox : (fun s => lam s + (ν s : ℝ)) ∈ Box lam e := fun s => by
      rw [he]
      simpa using abs_ball hν s
    have hgν : PI.ZuckTensor.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) (fun s => lam s + (ν s : ℝ))
        (Cg * Y - 2 * e) := gap_of_box hbox hgap (by linarith only)
    have hDS := hfam ν (hν1.trans (by omega))
    have hexp : ∀ a₁, a₁ ≤ 40 * (P.r + 1) ^ 2 → BigCellDerivativeExpansion p F b (C / 2 + 6) a₁ := fun a₁ ha₁ =>
      (H91 a₁ (R ν) F (coefOf_of_wsp hU hK hgν (hn ▸ g1) (R ν) hDS hF)).1 ν
        (by have := Nat.mul_le_mul_left (P.r + 1) ha₁; omega) hDS
    rcases hcase with ⟨hlen, hDD⟩ | ⟨huu, l, hl1, hlk, hposition⟩
    · have hn₀ : 2 * (2 * (P.r + 1)) + 0 ≤ 40 * (P.r + 1) ^ 2 := by nlinarith only [Nat.zero_le P.r]
      exact bp_max hb1 (le_max_of_le_left (le_max_left _ _)) hn₀ (H1 Wp Wq P p F b _ lam _ _ _ _ _ _ hF hbox
        (g3 _ hd1) hgν (g2 _ _ (by linarith only [q1, p3]) hd1) hL hTy hTy' hTT hTq hlen (by omega) hp₀ hDD (hexp _ hn₀)) γ hγ hG
    · have hn₀ : 2 * (2 * (P.r + 1)) + (30 * (P.r + 1) ^ 2 + 6) ≤ 40 * (P.r + 1) ^ 2 := by nlinarith only [Nat.zero_le P.r]
      exact bp_max hb1 (le_max_of_le_left (le_max_right _ _)) hn₀ (H2 Wp Wq P p F b _ _ l lam _ _ _ _ _ _ hF hbox
        (g3 _ hd2) hgν (g2 _ _ (by linarith only [q2, p2]) hd2) hL hTy huu hTT hTq rfl hl1 hlk (by push_cast; exact hposition) (by omega) hp₀
        (hexp _ hn₀)) γ hγ hG
  obtain ⟨-, -, -, s4, s5, s6, s7⟩ := hS
  have hXA : (|c₃| + 46) * thrX P.k P.r ≤ (|c₃| + 46) * thrX P.k P.r + e := by linarith only [he0]
  have hmain := HW hZ hZd hK s4 s5 s6 s7 P Wp Wq p f _ lam j hj a ((|c₃| + 46) * thrX P.k P.r + e) (Cg * Y)
    (fun γ => ENNReal.ofReal (b ^ (max (max C₁ C₂) 0 * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) *
      max 1 (1 / TBB.Gp p γ) ^ (40 * (P.r + 1) ^ 2))) hf hgap (by rw [← he]; linarith only [g4, g5, he0])
    (he ▸ kDecay_of_gap hZ P.k P.r _ g5 he0 g4)
    (thr_AB _ _ (by linarith only [a3]) hXA)
    (thr_conv _ _ (by linarith only [le_abs_self c₃]) (by linarith only [a3]) hXA) γ hγ hG hB
  have h00 : BranchingSupport.n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [BranchingSupport.n1]
  have hDS0 : (R 0).IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) lam := by simpa using hfam 0 h00
  have hcf : BallW.CoefOf (R 0) f := by
    obtain ⟨F₀, hF₀, hF₁⟩ := kfin_wsp hf
    intro l l'
    obtain ⟨s, w, x, y, X, h1, h2, h3⟩ := coefOf_of_wsp hU hK hgap (by rw [← hn]; linarith only [g1, he0]) (R 0) hDS0 hF₀ l l'
    exact ⟨s, w, x, y, X, h1, fun g hg => (hF₁ g hg).symm.trans (h2 g hg), h3⟩
  have hmom := (H91 a (R 0) f hcf).2 j hj (by omega) hDS0
  refine hmain.trans ((mul_le_mul' le_rfl hmom).trans ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have c1 : ((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ^ (2 * ((P.r + 1) * a)) ≤ b ^ (4 * |Ca| * m ^ 5) := by
    have h1 : ((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ≤ b ^ 2 := by
      push_cast
      nlinarith only [hn', hnb, hb3]
    calc _ ≤ (b ^ 2) ^ (2 * ((P.r + 1) * a)) := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 _
      _ = b ^ (4 * e) := by
        rw [← pow_mul, ← Real.rpow_natCast, he]
        congr 1
        push_cast
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb1 (by linarith only [hem, mul_le_mul_of_nonneg_left hm45 a4])
  have c2 : b ^ (max (max C₁ C₂) 0 * m ^ 4) ≤ b ^ (max (max C₁ C₂) 0 * m ^ 5) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_left hm45 a5)
  have c3 : b ^ ((C + 12) * m ^ 2 * a) ≤ b ^ ((C + 12) * |Ca| * m ^ 5) := by
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    calc (C + 12) * m ^ 2 * a ≤ (C + 12) * m ^ 2 * (|Ca| * m ^ 3) := mul_le_mul_of_nonneg_left ha' (mul_nonneg (by linarith only [hC]) (sq_nonneg _))
      _ = _ := by ring
  rw [← hm, add_mul _ _ (m ^ 5), add_mul _ _ (m ^ 5), Real.rpow_add hb0, Real.rpow_add hb0]
  calc _ = (((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ^ (2 * ((P.r + 1) * a)) * b ^ (max (max C₁ C₂) 0 * m ^ 4) *
        b ^ ((C + 12) * m ^ 2 * a)) * max 1 (1 / TBB.Gp p γ) ^ (40 * (P.r + 1) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul c1 c2 (by positivity) (by positivity)) c3 (by positivity) (by positivity))
        (by positivity)

end CompanionTheory.WaveGrid.WEnd
