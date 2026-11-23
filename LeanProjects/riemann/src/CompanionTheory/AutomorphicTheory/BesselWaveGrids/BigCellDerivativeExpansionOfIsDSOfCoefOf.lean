import CompanionTheory.AutomorphicTheory.BesselWaveGrids.FamilyThroughDiscreteSeries

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset CompanionTheory.WaveGrid.Ball
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.BallW

def CoefOf {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (R : Rep k r) (F : Mx k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (l : R.H → Wp) (l' : R.H → Wq), ∃ s, IsCoef R l l' F s

theorem suppliedData_existsW : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → Num P.k P.r lam P.u b bv ga h q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → CoefOf R0 f → TBB.jN2 p f ≠ 0 → ∃ (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (t : ℝ), 0 < t ∧ J ν₀ = (fun g => (t : ℂ) • f g) ∧ Sup0 p lam q0 R l l' dg s J tau := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R0 f ν₀ h0 hN hR0 hf hj
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨R, hfam, hR⟩ := family_through_discreteSeries hH P.k P.r lam P.u b bv ga h q0 R0 ν₀ hN hR0
  subst hR
  obtain ⟨l, l', dg, hl, hl'⟩ := GlobalTheory.T.exists_family_functionals hH P Wp Wq p lam b bv ga h q0 R hN hfam
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨s₀, hs₀⟩ := hf (l ν₀) (l' ν₀)
  obtain ⟨⟨-, -, -, -, hgap⟩, hnum⟩ := GlobalTheory.T.numericalFamily_shape_gaps P.k P.r lam P.u b bv ga h q0 hN
  have hg : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) (h / 2) :=
    (hnum ν₀ h0).2.2.1
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.bessel_setting_uniform_constant hH P.k P.r Wp Wq p.T.base
  have hne : s₀ ≠ 0 := by
    intro hz
    apply hj
    rw [GlobalTheory.T.jN2_eq_normSq_base P Wp Wq p f,
      hc _ _ (h / 2) (R ν₀) (l ν₀) (l' ν₀) (dg ν₀) hR0 hg hgap (hl ν₀ h0).1 (hl' ν₀ h0).1 (hl ν₀ h0).2.2 f s₀ hs₀, hz]
    simp
  obtain ⟨s, J, t, ht, hJ, -, hcoef, hzero⟩ :=
    exists_coef_family hH P Wp Wq p lam b bv ga h q0 R l l' dg f s₀ ν₀ h0 hfam hl hl' hs₀ hne
  obtain ⟨tau, htau⟩ :=
    exists_tau hH P Wp Wq p lam b bv ga h q0 R l l' dg s J hN hfam hl hl' hcoef hzero
  exact ⟨R, l, l', dg, s, J, tau, t, ht, hJ, htau⟩

theorem coef_norm_finite_and_zeroW : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ), n1 ν₀ ≤ q0 → Num P.k P.r lam P.u b bv ga h q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → CoefOf R0 f → TBB.jN2 p f < ⊤ ∧ (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) ∧ (TBB.jN2 p f = 0 → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R0 f ν₀ h0 hN hR0 hf
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨R, hfam, hR⟩ := family_through_discreteSeries hH P.k P.r lam P.u b bv ga h q0 R0 ν₀ hN hR0
  subst hR
  obtain ⟨l, l', dg, hl, hl'⟩ := GlobalTheory.T.exists_family_functionals hH P Wp Wq p lam b bv ga h q0 R hN hfam
  obtain ⟨hB, hdg, hfd⟩ := hl ν₀ h0
  obtain ⟨hB', -, -⟩ := hl' ν₀ h0
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  have hgap : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) (h / 2) :=
    (hν ν₀ h0).2.2.1
  obtain ⟨s, hs⟩ := hf (l ν₀) (l' ν₀)
  obtain ⟨c, hc, hnorm⟩ := GlobalTheory.T.bessel_setting_uniform_constant hH P.k P.r Wp Wq p.T.base
  have hj : TBB.jN2 p f = ENNReal.ofReal (c * ‖s‖ ^ 2 / dg ν₀) := by
    rw [GlobalTheory.T.jN2_eq_normSq_base]
    exact hnorm _ _ (h / 2) (R ν₀) (l ν₀) (l' ν₀) (dg ν₀) hR0 hgap hok hB hB' hfd f s hs
  have hck := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH P.k P.r _ _ (h / 2) (R ν₀) Wp Wq (l ν₀) (l' ν₀) f s hR0 hgap hok hs).1
  refine ⟨by rw [hj]; exact ENNReal.ofReal_lt_top,
    GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell P Wp Wq p f (GlobalTheory.CoefZero.continuousOn_of_ckOn hck), fun hz x hx hG => ?_⟩
  have hs0 : s = 0 := by
    by_contra hne
    rw [hj, ENNReal.ofReal_eq_zero] at hz
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hne
    have : 0 < c * ‖s‖ ^ 2 / dg ν₀ := by positivity
    linarith
  obtain ⟨γ, hγ, -, hV⟩ := GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel P Wp Wq p x hx hG
  obtain ⟨OO, hOO⟩ := GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul hH P.k P.r _ _ (h / 2) (R ν₀) Wp Wq p.T.base (l ν₀) (l' ν₀) hR0 hgap hok hB hB'
  rw [hV f, (hOO f s hs γ hγ).2, hs0, zero_smul]

theorem familyDerivativeExpansion_of_isDS_of_coefOf (H : Hyps) (C : ℝ) (hC : 0 ≤ C) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ)
    (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ)
    (hN : Num P.k P.r lam P.u b bv ga h q0) (hN' : Num P.k P.r lam P.u' b bv ga h q0)
    (hT : P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ))) (hT' : P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)))
    (hq : n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0)
    (hDS : R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)))
    (hf : CoefOf R0 f) :
    Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  obtain ⟨⟨hbv, hbv', hn', -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hN
  have hb : 2 ≤ b := by linarith
  have hν₀ : n1 ν₀ ≤ q0 := by omega
  obtain ⟨hfin, hmeas, hz⟩ := coef_norm_finite_and_zeroW H P Wp Wq p lam b bv ga h q0 R0 f ν₀ hν₀ hN hDS hf
  by_cases h0 : TBB.jN2 p f = 0
  · exact GlobalTheory.T.familyDerivativeExpansion_of_V_eq_zero P Wp Wq p f b _ a₁ (by linarith) hmeas (hz h0)
  obtain ⟨R, l, l', dg, s, J, tau, t, ht, hJ, hS⟩ :=
    suppliedData_existsW H P Wp Wq p lam b bv ga h q0 R0 f ν₀ hν₀ hN hDS hf h0
  have hn : ∀ μ : Fin (2 * P.r + P.k + 1) → ℤ, n1 μ ≤ Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.N1 (μ - ν₀) + n1 ν₀ := fun μ => by
    have e : Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.N1 (μ - ν₀ + ν₀) ≤ _ := Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.n1_add_le (μ - ν₀) ν₀
    rw [sub_add_cancel] at e
    exact e
  let d : Formalism.FourierDecayAlt.P.CutBP.PieriExpansionData P Wp Wq :=
    ⟨(2 * P.r + P.k + 1), J, ν₀, tau, (P.r + 1) * (P.r + 2), q0 - n1 ν₀, Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b)⟩
  have hP : Formalism.FourierDecayAlt.P.CutBP.PieriExpansion p d := fun μ hμ c hc hG =>
    supplied_pieri H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS μ
      (by have := hn μ; dsimp only [d] at hμ; omega) c hc hG
  have hTau : Formalism.FourierDecayAlt.P.CutBP.PieriCoefficientBound d := fun μ hμ I hI =>
    tau_bound H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hN' hS μ
      (by have := hn μ; dsimp only [d] at hμ; omega) I (Finset.mem_powersetCard.1 hI).2
  have hD : Formalism.FourierDecayAlt.P.CutBP.PieriDegreeConditions p d := by
    obtain ⟨c, hc, key⟩ := sup_norm H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS
    have hdeg := GlobalTheory.FamilyDegreeRatio.degree_ratios P.k P.r lam P.u b bv ga h q0 hN
    dsimp only [d]
    refine ⟨?_, ?_, ?_⟩
    · show 0 < TBB.jN2 p (J ν₀)
      rw [hJ, Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul]
      refine ENNReal.mul_pos ?_ h0
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos (norm_pos_iff.2 (Complex.ofReal_ne_zero.2 ht.ne')) 2
    · intro μ hμ
      have hμ' : n1 μ ≤ q0 := by have := hn μ; dsimp only at hμ; omega
      show TBB.jN2 p (J μ) < ⊤ ∧ (TBB.jN2 p (J μ) = 0 → ∀ c : Fin (P.r + 1) → ℂ,
        D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V (J μ) (TBB.bigPt P.r c) = 0)
      rcases key μ hμ' with ⟨hJ, hz, -⟩ | ⟨-, -, -, -, he⟩
      · refine ⟨by rw [hz]; exact ENNReal.zero_lt_top, fun _ x _ _ => ?_⟩
        have e : J μ = fun g => (0 : ℂ) • J μ g := by
          funext g
          rw [hJ, zero_smul]
          rfl
        rw [e, Formalism.FourierDecayAlt.P.CutBP.V_csmul, zero_smul]
      · refine ⟨by rw [he]; exact ENNReal.ofReal_lt_top, fun hz => ?_⟩
        rw [he] at hz
        exact absurd hz (ENNReal.ofReal_pos.2 (mul_pos hc (hdeg μ hμ').1)).ne'
    · intro μ hμ hne I hI
      have hμ1 : n1 μ + (P.r + 1) * (P.r + 2) ≤ q0 := by have := hn μ; dsimp only at hμ; omega
      have hμ' : n1 μ ≤ q0 := le_trans (Nat.le_add_right _ _) hμ1
      have hcard : I.card = P.r + 1 := (mem_powersetCard.1 hI).2
      have hν : n1 (μ + eZ I) ≤ q0 := by
        have e1 : n1 (μ + eZ I) ≤ n1 μ + Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.N1 (Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.eI I) :=
          Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.n1_add_le μ (Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.eI I)
        rw [Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.n1_eI_eq_card, hcard] at e1
        have e2 : P.r + 1 ≤ (P.r + 1) * (P.r + 2) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      change TBB.jN2 p (J μ) ≠ 0 at hne
      show TBB.jN2 p (J (μ + eZ I)) ≤
        ENNReal.ofReal ((Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1)) * TBB.jN2 p (J μ)
      rcases key μ hμ' with ⟨-, hz, -⟩ | ⟨-, -, -, -, he⟩
      · exact absurd hz hne
      rcases key _ hν with ⟨-, hz, -⟩ | ⟨-, -, -, -, he'⟩
      · rw [hz]; exact zero_le
      rw [he, he', ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      obtain ⟨hpos, hrat, -⟩ := hdeg μ hμ'
      have e1 := hrat I
      rw [hcard] at e1
      have e2 : ((2 * P.r + P.k + 1) : ℝ) ^ (P.r + 1) ≤ (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        push_cast
        exact le_mul_of_one_le_left (by positivity) (Real.one_le_exp zero_le_one)
      have e3 := e1.trans (mul_le_mul_of_nonneg_right e2 hpos.le)
      calc _ ≤ c * (_ * _) := mul_le_mul_of_nonneg_left e3 hc.le
        _ = _ := by ring

  have hM := sup_meas H P Wp Wq p lam b bv ga h q0 R l l' dg s J tau hN hS
  have hH := GlobalTheory.TopNum.top_num P.r P.T P.T' b C hC hb hT hT'
  have hE := Formalism.FourierDecayAlt.P.CutBP.family_expansion_of_parts p (Formalism.FourierDecayAlt.P.CutBP.unitF p (J ν₀)) b (C / 2 + 6) a₁ d
    rfl (Real.sqrt_nonneg _) (Nat.le_mul_of_pos_right _ (by omega)) (by dsimp only [d]; omega)
    (Formalism.FourierDecayAlt.P.CutBP.coefficient_growth_le_power _ P.r b _ (C + 10) _ hb (by dsimp only [d]; push_cast; exact hn') (Real.sqrt_nonneg _) hH (by linarith))
    hP hTau hD hM
  have hpos : 0 < TBB.jN2 p (J ν₀) := hD.1
  have hlt : TBB.jN2 p (J ν₀) < ⊤ := (hD.2.1 ν₀ (by simp [Formalism.FourierDecayAlt.P.CutBP.LatticeNorms.N1, d])).1
  have hsc : Formalism.FourierDecayAlt.P.CutBP.scF p (J ν₀) ≠ 0 := by
    unfold Formalism.FourierDecayAlt.P.CutBP.scF
    exact inv_ne_zero (Real.sqrt_pos.2 (ENNReal.toReal_pos hpos.ne' hlt.ne)).ne'
  have hE' := GlobalTheory.T.bigCellExpansion_smul P Wp Wq p _ b _ a₁ (((Formalism.FourierDecayAlt.P.CutBP.scF p (J ν₀) : ℂ) * (t : ℂ))⁻¹) hE
  have hne : ((Formalism.FourierDecayAlt.P.CutBP.scF p (J ν₀) : ℂ) * (t : ℂ)) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hsc) (Complex.ofReal_ne_zero.2 ht.ne')
  have e : (fun g => (((Formalism.FourierDecayAlt.P.CutBP.scF p (J ν₀) : ℂ) * (t : ℂ))⁻¹) • Formalism.FourierDecayAlt.P.CutBP.unitF p (J ν₀) g) = f := by
    funext g
    have hg : J ν₀ g = (t : ℂ) • f g := congrFun hJ g
    unfold Formalism.FourierDecayAlt.P.CutBP.unitF
    rw [hg, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hne, one_smul]
  rw [e] at hE'
  exact hE'

theorem bigCellDerivativeExpansion_of_isDS_of_coefOf (H : Hyps) (C : ℝ) (hC : 0 ≤ C) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ)
    (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ)
    (hN : Num P.k P.r lam P.u b bv ga h q0) (hN' : Num P.k P.r lam P.u' b bv ga h q0)
    (hT : P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ))) (hT' : P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)))
    (hq : n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0)
    (hDS : R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)))
    (hf : CoefOf R0 f) :
    Formalism.FourierDecayAlt.P.CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  have hb := (GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN).1
  exact Formalism.FourierDecayAlt.P.CutBP.big_cell_expansion_of_family p f b (C / 2 + 6) a₁ (by linarith [hb.1, hb.2.1])
    (familyDerivativeExpansion_of_isDS_of_coefOf H C hC P Wp Wq p lam b bv ga h q0 a₁ R0 f ν₀ hN hN' hT hT' hq hDS hf)

end CompanionTheory.WaveGrid.BallW
