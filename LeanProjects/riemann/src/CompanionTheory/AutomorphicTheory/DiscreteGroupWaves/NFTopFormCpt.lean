import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StepFormCptAllOfStepFormAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFTopCpt

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ordM (P : M.Par) (N : ℕ) : ℕ := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5)

theorem residue_zero_bound : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ), C6.IsCut0 χ → 0 < ε →
    Cs * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    ∀ w : List C.Letter, w.length ≤ N → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle A (ordM P N) h c →
        ‖p.RR (D.cutF p.T.base χ h ε) 0 w [] []‖ ≤ K * c ^ 2 := by
  obtain ⟨Cs, hCs0, hSQ⟩ := PBE.sliceQ
  refine ⟨Cs, hCs0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p χ ε A N hχ hε hA w hw
  have hk2 : 2 ≤ P.k := p.hl.2.2
  have hloc : D.IsLocPt ([] : C.LPt) 0 := ⟨by simp, rfl⟩
  have hc : P.r - 0 = P.r - D.ptSize ([] : C.LPt) := rfl
  have hQ := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ A N P rfl rfl hk2 hχ hA ε hε 0 (Nat.zero_le _) w hw [] hc
    hloc e
  choose εa Ka hεa hKa hQ1 _ using hQ
  set KK : ℝ := ∑ e, Ka e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := fun e => Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun e _ => hKa e
  have hAu : P5.Auser P w.length + 1 ≤ P5.Auser P N + 1 := by linarith [PBE.auser_mono P hw]
  obtain ⟨Cf, hCf0, hCf⟩ := JCx4.formLev_bound_mm P p.T (M.sgn P p.l0) ⟨0, by omega⟩ w (P5.Auser P N + 1 + 1)
    (by linarith)
  have hmm5 : 5 + (2 * (P.r - 0) + P.k + 1) * w.length ≤ P5.mmUser P N := by
    have := JCx2.pd_thr_mm P ⟨0, by omega⟩ N (P5.mmUser P N) le_rfl
    have h2 : (2 * (P.r - 0) + P.k + 1) * w.length ≤ (2 * (P.r - 0) + P.k + 1) * N := Nat.mul_le_mul_left _ hw
    simp only at this
    omega
  have h5 : 5 ≤ P5.mmUser P N := by unfold P5.mmUser; omega
  refine ⟨Cf * KK ^ 2, by positivity, fun h c hh hcc => ?_⟩
  have hc0 : 0 ≤ c := JCx2.pd_ccle_nonneg hcc
  have hx : ∀ e, B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h e) (KK * c) :=
    fun e => JCx2.pd_ccle_mono_c (hQ1 e h c hh hcc).2 (mul_le_mul_of_nonneg_right (hKa' e) hc0)
  have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have hb := hCf (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h) (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h)
    (KK * c) (KK * c) (fun e => BetaSesquilinearity.CCle_mono_A (by linarith) (BetaSesquilinearity.CCle_mono_m hmm5 (hx e)))
    (fun e => BetaSesquilinearity.CCle_mono_A (by linarith) (BetaSesquilinearity.CCle_mono_m h5 (hx e)))
  have e : p.RR (D.cutF p.T.base χ h ε) 0 w [] [] = D.formLev p.T (M.sgn P p.l0) ⟨0, by omega⟩ w
      (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h) (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h) := by
    unfold KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hloc, hloc⟩, dif_pos (Nat.zero_le _)]
    rfl
  rw [e]
  exact hb.trans (le_of_eq (by ring))

theorem topForm_cut (hPS : StandardPairingDecay.PStdC) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    ∀ w, KB.CutWord P p.l0 w → w.length ≤ N →
      Integrable (topD p (D.cutF p.T.base χ f ε) w) ∧
        ∫ c, topD p (D.cutF p.T.base χ f ε) w c = (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re := by
  obtain ⟨Cs, hCs0, hB⟩ := residue_zero_bound
  obtain ⟨Cl, hL⟩ := limit_of_module_forms Cb
  refine ⟨max (Cs + 1) Cl, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N hCb hχ hε hf hfA hA w hw hwN
  set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  have hmono : ∀ c, c ≤ max (Cs + 1) Cl → c * ((P.r : ℝ) + 1) ^ 4 * X ≤ A := fun c hc =>
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)) hA
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1 := by
    have h1 := hmono _ (le_max_left _ _)
    have h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X := by nlinarith
    nlinarith
  obtain ⟨hcpt, hlim⟩ := hL Wp Wq P p f χ ε A N (cutN P.k P.r) hCb hχ hε hf hfA (hmono _ (le_max_right _ _))
    (fun _ _ => rfl)
  obtain ⟨K, hK0, hK⟩ := hB Wp Wq P p χ ε (A - 1) N hχ hε hA' w hwN
  obtain ⟨bf, hbf⟩ := hfA (ordM P N)
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) (ordM P N)
  have hψ : ∀ n : ℕ, B.CCle (A - 1) (ordM P N) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g)
      (Kp * bf / ((n : ℝ) + 1)) := fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf
  set H : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g with hH
  have hdiff : ∀ n m : ℕ, (fun g => H n g - H m g) = D.cutF p.T.base χ
      (fun g => JCx2.pdPsi ((m : ℝ) + 1) g • f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g)) ε := by
    intro n m
    funext g
    simp only [hH, D.cutF, PBE.cut_eq (cutN P.k P.r) (fun _ _ => rfl)]
    module
  have hdc : ∀ n m, KB.CptCoef p.T.base (fun g => H n g - H m g) := fun n m => PBN.cpt_sub _ (hcpt n) (hcpt m)
  have hd : ∀ n m : ℕ, ∫ c, topD p (fun g => H n g - H m g) w c ≤
      K * (Kp * bf / ((m : ℝ) + 1) + Kp * bf / ((n : ℝ) + 1)) ^ 2 := by
    intro n m
    rw [(topForm_cpt hPS p hCb hw (hdc n m)).2, hdiff]
    refine (Complex.re_le_norm _).trans (hK _ _ (BetaSesquilinearity.CkOn_add (hψs m) (BetaSesquilinearity.CkOn_smul (-1) (hψs n))) ?_)
    have := BetaSesquilinearity.CCle_add (hψ m) (BetaSesquilinearity.CCle_smul (-1) (hψ n))
    simpa using this
  refine integral_eq_of_sqrt_cauchy (q := fun n => topD p (H n) w) (d := fun n m => topD p (fun g => H n g - H m g) w)
    (fun n => (topForm_cpt hPS p hCb hw (hcpt n)).1) (fun n c => ew_top_nonneg p _ w _)
    (fun n m => (topForm_cpt hPS p hCb hw (hdc n m)).1) (fun n m c => ew_top_nonneg p _ w _)
    (fun n m c => topD_tri p hCb hw (hcpt n) (hcpt m) c) (Eventually.of_forall fun c => ?_) ?_ ?_
  · unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp ((hlim (P.r + 1) w hw hwN _ _).const_mul _)
  · exact ((Complex.continuous_re.tendsto _).comp (hlim 0 w hw hwN [] [])).congr
      fun n => (topForm_cpt hPS p hCb hw (hcpt n)).2.symm
  · intro η hη
    have h1 : Tendsto (fun n : ℕ => K * (2 * (Kp * bf / ((n : ℝ) + 1))) ^ 2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => Kp * bf / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      simpa using ((h0.const_mul 2).pow 2).const_mul K
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h1.eventually (ge_mem_nhds hη))
    refine ⟨N₀, fun n m hn hm => (hd n m).trans (le_trans ?_ (hN₀ N₀ le_rfl))⟩
    have hb : ∀ j : ℕ, N₀ ≤ j → Kp * bf / ((j : ℝ) + 1) ≤ Kp * bf / ((N₀ : ℝ) + 1) := fun j hj =>
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast Nat.succ_le_succ hj)
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 2) hK0
    linarith [hb n hn, hb m hm]

def NFTopFormAllCpt : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopForm p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

theorem top_form_all_compact : NFTopFormAllCpt := by
  intro hA Cb
  obtain ⟨Cc, hC⟩ := topForm_cut (StandardPairingDecay.pStdC_of hA radial_head head_top) Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  obtain ⟨hχ, hCb, hf, hfA, hth, -⟩ := hH
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  exact (hC Wp Wq P p _ χ ε _ N hCb hχ hε (ckOn_fpm p p₀ hf hid) (inCC_fpm_id p p₀ hfA) hth w hw.1 hN).2.symm

end

end CompanionTheory.NFCpt
