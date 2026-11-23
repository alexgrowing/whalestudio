import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.ThetaInZIsThetaLog
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementC
import Formalism.GaussJetBounds.ThmAEntryFull
import Formalism.GaussJetBounds.OneLetterGauss
import Formalism.GaussJetBounds.ThmAGauss
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.ThetaLogIsSubst
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK lamF thetaLog sSub zLin)

theorem unramified_top : UnramTop := by
  intro K _ l σ hU a _ ha
  obtain ⟨k, hk⟩ := hU.2.2.2.1 a ha
  refine ⟨-k, ?_⟩
  rw [hk, hU.2.2.1, inv_zpow', neg_neg]

namespace CohomologyFunctoriality₂

theorem norm_iter {K0 : Type} [NormedField K0] [IsUltrametricDist K0] [CharZero K0] {l : ℕ}
    {σ : K0 →+* K0} (hU : UnrOK K0 l σ) {c : K0} (hc : ‖c‖ ≤ 1) (n : ℕ) : ‖σ^[n] c‖ ≤ 1 := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (frobSq K0 l σ hU).2 _ ih

theorem frob_step {K0 K : Type} [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    [NormedField K] {l d : ℕ} [NeZero d] {σ : K0 →+* K0} (j : K0 →+* K) (hU : UnrOK K0 l σ)
    (hj : ∀ a, ‖j a‖ = ‖a‖) {c : K0} (hc : ‖c‖ ≤ 1) (hfix : σ^[d] c = c) (s : ZMod d) :
    ‖j (σ^[(s + 1).val] c) - j (σ^[s.val] c) ^ l‖ ≤ (l : ℝ)⁻¹ := by
  have h := TranslateJetMomentLawAnyIdempotentLevel.iter_sub_one σ hfix (s + 1)
  rw [add_sub_cancel_right] at h
  rw [← h, ← map_pow, ← map_sub, hj]
  exact hU.2.2.2.2 _ (norm_iter hU hc _)

end CohomologyFunctoriality₂

theorem omega_integral_criterion : OmOKOf := by
  intro K0 K _ _ _ _ l ν _ σ j hU hj om oms hO hT
  refine ⟨fun r s => ?_, fun r s => ?_, fun a b hab => ?_⟩
  · unfold conjJ
    rw [hj, hj]
    exact ⟨CohomologyFunctoriality₂.norm_iter hU (hO.1 r).1 _, CohomologyFunctoriality₂.norm_iter hU (hO.1 r).2 _⟩
  · unfold conjJ
    exact ⟨CohomologyFunctoriality₂.frob_step j hU hj (hO.1 r).1 (hO.2 r).1 s,
      CohomologyFunctoriality₂.frob_step j hU hj (hO.1 r).2 (hO.2 r).2 s⟩
  · unfold conjJ
    have hE : Even (2 * ν) := even_two_mul ν
    have key : ∑ r, σ^[a.val] (oms r) * σ^[b.val] (om r) = if a = b then 1 else 0 := by
      by_cases ha : a.val % 2 = 0
      · have hb : b.val % 2 = 0 := by omega
        have h := TranslateJetMomentLawAnyIdempotentLevel.dual2 hE σ hO.2 hT b a
        rw [Fintype.sum_prod_type, Fintype.sum_bool] at h
        simp only [mXY, TranslateJetMomentLawAnyIdempotentLevel.pXY, ha, hb, if_true] at h
        simp only [Bool.true_eq_false, if_false, mul_zero, Finset.sum_const_zero, zero_add] at h
        have e : (if a = b then (1 : K0) else 0) = if b = a then 1 else 0 := by
          by_cases hab' : a = b
          · rw [if_pos hab', if_pos hab'.symm]
          · rw [if_neg hab', if_neg (fun h => hab' h.symm)]
        rw [e, ← h]
        exact Finset.sum_congr rfl fun r _ => mul_comm _ _
      · have hb : ¬ b.val % 2 = 0 := by omega
        have h := TranslateJetMomentLawAnyIdempotentLevel.dual2 hE σ hO.2 hT a b
        rw [Fintype.sum_prod_type, Fintype.sum_bool] at h
        simp only [mXY, TranslateJetMomentLawAnyIdempotentLevel.pXY, ha, hb, if_false] at h
        simp only [Bool.false_eq_true, if_false, mul_zero, Finset.sum_const_zero, add_zero,
          if_true] at h
        exact h
    have h2 := congrArg j key
    rw [map_sum] at h2
    simp only [map_mul] at h2
    rw [h2]
    split_ifs <;> simp

theorem theta_integer_is_s_substitution : ThetaInZIsSSub := by
  intro K0 K _ _ l ν r0 r1 _ σ j om oms Tht
  unfold thetaInZ
  congr 1
  funext x
  unfold xOfZ Formalism.InvariantFactorPaths.G7.sSub Formalism.InvariantFactorPaths.G7.zLin conjJ
  congr 1
  by_cases h : x.1 = false
  · simp only [h, if_true]
  · simp only [h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases Nat.mod_two_eq_zero_or_one s.val with h2 | h2 <;> simp [h2]

namespace CohomologyFunctoriality₂

open Formalism.InvariantFactorPaths.G7 Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution

theorem log_scale {K : Type} [Field K] (p : ℕ) (ϖ : K) (μ : PowerSeries K)
    (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X) :
    (PowerSeries.subst (PowerSeries.C ϖ * μ) (lgF K p) : PowerSeries K) =
      PowerSeries.C ϖ * PowerSeries.X := by
  have e1 := LogarithmEquivalence.subst_lgF_scale p ϖ
  have hμ : PowerSeries.HasSubst μ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hX : PowerSeries.HasSubst (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have e2 := congrArg (fun f => (PowerSeries.subst μ f : PowerSeries K)) e1
  rw [PowerSeries.subst_comp_subst_apply hX hμ] at e2
  rw [← PowerSeries.coe_substAlgHom hμ, map_mul, map_mul, PowerSeries.coe_substAlgHom hμ, h1,
    PowerSeries.subst_X hμ] at e2
  have e3 : (PowerSeries.substAlgHom hμ) (PowerSeries.C ϖ : PowerSeries K) = PowerSeries.C ϖ := by
    have : (PowerSeries.C ϖ : PowerSeries K) = algebraMap K _ ϖ := rfl
    rw [this, AlgHom.commutes]
  rw [PowerSeries.coe_substAlgHom hμ] at e3
  rw [e3] at e2
  exact e2

theorem log_coord {K : Type} [Field K] (p ν r0 r1 : ℕ) [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K) (μ : PowerSeries K) (x : Bool × EV ν r0 r1)
    (hϖ : ϖ ≠ 0) (hμ0 : PowerSeries.constantCoeff μ = 0)
    (hμ : (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X) :
    PowerSeries.subst (MvPowerSeries.subst
        (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (MvPowerSeries.C ϖ * sSub om oms μ x)) (lgF K p) = zLin om oms x := by
  have hb := hasSubst_scale (K := K) (ι := ZV ν r0 r1) ϖ⁻¹
  have hz : PowerSeries.HasSubst (zLin om oms x : MvPowerSeries (ZV ν r0 r1) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_zLin om oms x)
  have hw : PowerSeries.HasSubst
      (MvPowerSeries.C ϖ⁻¹ * zLin om oms x : MvPowerSeries (ZV ν r0 r1) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_mul, constantCoeff_zLin, mul_zero])
  have hm : PowerSeries.HasSubst (PowerSeries.C ϖ * μ : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by rw [map_mul, hμ0, mul_zero])
  have e1 : MvPowerSeries.subst
      (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
      (MvPowerSeries.C ϖ * sSub om oms μ x) =
      PowerSeries.subst (MvPowerSeries.C ϖ⁻¹ * zLin om oms x) (PowerSeries.C ϖ * μ) := by
    rw [subst_C_mul hb, ps_subst_C_mul hw]
    unfold sSub
    rw [FormalGroupLaws.subst_subst hb hz, subst_scale_zLin]
  have e2 := congrArg (fun f => (PowerSeries.subst (MvPowerSeries.C ϖ⁻¹ * zLin om oms x) f :
    MvPowerSeries (ZV ν r0 r1) K)) (log_scale p ϖ μ hμ0 hμ)
  rw [PowerSeries.subst_comp_subst_apply hm hw, ps_subst_C_mul hw ϖ PowerSeries.X,
    PowerSeries.subst_X hw,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖ, map_one, one_mul] at e2
  rw [e1]
  exact e2

end CohomologyFunctoriality₂

theorem theta_integer_is_theta_log : ThetaInZIsThetaLog := by
  intro K0 K _ _ l ν r0 r1 _ σ j om oms ϖ μ hl hϖ hμ0 hμ Tht
  rw [theta_integer_is_s_substitution, Formalism.InvariantFactorPaths.G7.Top.thetaLogIsSubst K ν r0 r1 _ _ ϖ μ Tht hμ0]
  congr 1
  funext x
  have hb := Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.hasSubst_scale (K := K) (ι := Formalism.InvariantFactorPaths.G7.ZV ν r0 r1) ϖ⁻¹
  have hcc : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      (fun y => MvPowerSeries.C ϖ⁻¹ *
        (MvPowerSeries.X y : MvPowerSeries (Formalism.InvariantFactorPaths.G7.ZV ν r0 r1) K))
      (MvPowerSeries.C ϖ * sSub (conjJ j σ om) (conjJ j σ oms) μ x)) = 0 := by
    refine MvPowerSeries.constantCoeff_subst_eq_zero hb (fun i => by simp) ?_
    have h : MvPowerSeries.constantCoeff (sSub (conjJ j σ om) (conjJ j σ oms) μ x) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero
        (Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.constantCoeff_zLin _ _ x) μ hμ0
    rw [map_mul, h, mul_zero]
  have h := Pair.exp_log expSpec hl hcc
  rw [CohomologyFunctoriality₂.log_coord l ν r0 r1 _ _ ϖ μ x hϖ hμ0 hμ] at h
  exact h

namespace CohomologyFunctoriality₂

theorem thetaForm (l : ℕ) [Fact l.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0]
    [CharZero K0] (σ : K0 →+* K0) (hU : UnrOK K0 l σ) (j : K0 →+* ℂ_[l]) (hj : ∀ a, ‖j a‖ = ‖a‖)
    (F : MvPowerSeries (Fin 2) K0) (hF : IsLawOfLog l F) (be0 : MvPowerSeries (Fin 2) K0)
    (hF1 : F1 F be0) (hF2 : F2 l σ be0) (d N0 N1 : ℕ) [NeZero d] (hd2 : 2 ≤ d) (hde : Even d)
    (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0) (hO : OwOK d σ om oms)
    (hT : TrDual d σ om oms) (hζ : ∃ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1))
    (U0 Φ : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) ℂ_[l]) (hU0 : Integral U0)
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (hΦ : Simeq Φ (sumE (MvPowerSeries.map j be0))) :
    ∃ (K1 : Subfield ℂ_[l]) (ζ : ℂ_[l]) (be : MvPowerSeries (ZMod d) ℂ_[l])
      (g : Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) ℂ_[l])
      (U : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) ℂ_[l]),
      Unram l K1 ∧ IsPrimitiveRoot ζ (l ^ d - 1) ∧ BHyp l d K1 ζ be ∧
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) ∧
      (∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y) ∧ Integral U ∧
      thetaInZ l j σ om oms (mvExp (-Φ) * U0) = thetaZ g U (-1) be := by
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨U, hUi, hUeq⟩ := b0 K0 ℂ_[l] l d N0 N1 σ j hU hj hd2 hde F hF be0 hF1 hF2 ι om oms hO hT
    ζ hζ U0 Φ hU0 hΦ0 hΦ
  obtain ⟨g, hg0, hg, -⟩ := Formalism.DworkPowerSeriesWeights.generalized_log_inverse.{0, 0} ℂ_[l] l hU.1
    (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) (fun y => (y.1 - 2, y.2.1, y.2.2))
  have hg' : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y := by
    intro y
    rw [(Formalism.DworkPowerSeriesWeights.logarithm_weight_comparison.{0} ℂ_[l] l d N0 N1).2.1 y]
    exact hg y
  obtain ⟨hT1, hT2, -, -⟩ := Formalism.DworkPowerSeriesWeights.admissibleTransfer K0 ℂ_[l] j hj l d N0 N1 ⊤ ζ
    (beMean l σ be0 om oms ζ)
  exact ⟨_, j ζ, _, g, U, hT1 (unramified_top K0 l σ hU), hζ.map_of_injective j.injective,
    hT2 (biextension_hypotheses_of_level_one K0 l d σ hU hd2 hde F hF be0 hF1 ι om oms hO ζ hζ), hg0, hg', hUi,
    hUeq g hg0 hg'⟩

end CohomologyFunctoriality₂

theorem theorem_a_entry_of_f : ThmAEntryOfF := by
  intro l _ K0 _ _ _ σ hU j hj F hF be0 hF1 hF2 d N0 N1 _ hd2 hde ι _ _ om oms hO hT hζ U0 Φ hU0
    hΦ0 hΦ TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 a ha hsa hthr δ hδ
  obtain ⟨K1, ζ, be, g, U, hK1, hζ', hbe, hg0, hg, hUi, heq⟩ := CohomologyFunctoriality₂.thetaForm l K0 σ hU j hj F hF
    be0 hF1 hF2 d N0 N1 hd2 hde ι om oms hO hT hζ U0 Φ hU0 hΦ0 hΦ
  rw [heq]
  exact Formalism.DworkPowerSeriesWeights.thmAEntryFull l d N0 N1 hU.2.1 hd2 hde K1 hK1 ζ hζ' be hbe g hg0 hg U hUi (-1)
    (Or.inr rfl) TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 a ha hsa hthr δ hδ

theorem theorem_a_gauss_of_f : ThmAGaussOfF := by
  intro l _ K0 _ _ _ σ hU j hj F hF be0 hF1 hF2 d N0 N1 _ hd2 hde ι _ _ om oms hO hT hζ U0 Φ hU0
    hΦ0 hΦ TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 a ha hsa hthr n
  obtain ⟨K1, ζ, be, g, U, hK1, hζ', hbe, hg0, hg, hUi, heq⟩ := CohomologyFunctoriality₂.thetaForm l K0 σ hU j hj F hF
    be0 hF1 hF2 d N0 N1 hd2 hde ι om oms hO hT hζ U0 Φ hU0 hΦ0 hΦ
  rw [heq]
  exact Formalism.DworkPowerSeriesWeights.thmAGauss l d N0 N1 hU.2.1 hd2 hde K1 hK1 ζ hζ' be hbe g hg0 hg U hUi (-1)
    (Or.inr rfl) TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 a ha hsa hthr n

theorem one_letter_gauss_of_f : OneLetterGaussOfF := by
  intro l _ K0 _ _ _ σ hU j hj F hF be0 hF1 hF2 hζ ph hph N0 N1 C U0 Φ hU0 hΦ0 hΦ p hp I a ha hsa n
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨U, hUi, hUeq⟩ := single_letter_theta_factorization K0 ℂ_[l] l N0 N1 σ j hU hj F hF be0 hF1 hF2 ζ hζ ph hph U0 Φ hU0
    hΦ0 hΦ
  obtain ⟨g, hg0, hg, -⟩ := Formalism.DworkPowerSeriesWeights.generalized_log_inverse.{0, 0} ℂ_[l] l hU.1
    (Fin N0 × Fin N1) id
  have hg' : ∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y := by
    intro y
    rw [(Formalism.DworkPowerSeriesWeights.logarithm_weight_comparison.{0} ℂ_[l] l 2 N0 N1).2.2 y]
    exact hg y
  obtain ⟨hT1, hT2, -, -⟩ := Formalism.DworkPowerSeriesWeights.admissibleTransfer K0 ℂ_[l] j hj l 2 N0 N1 ⊤ ζ
    (beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1) ζ)
  rw [hUeq g hg0 hg']
  exact Formalism.DworkPowerSeriesWeights.oneLetterGauss l N0 N1 C hU.2.1 _ (hT1 (unramified_top K0 l σ hU)) (j ζ)
    (hζ.map_of_injective j.injective) _
    (hT2 (biextension_hypotheses_of_level_one K0 l 2 σ hU le_rfl (by decide) F hF be0 hF1 Unit _ _ (SingleLetterLog.owOK_two σ) ζ hζ))
    1 (by simp) g hg0 hg' U hUi (-1) (Or.inr rfl) p hp I a ha hsa n

theorem theorem_s_of_f : ThmSOfF := by
  intro K0 K _ _ _ _ _ _ _ j p ν r0 r1 _ σ hj hU hζ F hF be hF1 hF2
  obtain ⟨c, hc, hcc, h⟩ := Formalism.InvariantFactorPaths.G7.Top.thmSFull K0 K j p ν r0 r1 σ hj hU hζ F hF be
    (betaHypOfF K0 p σ hU F be hF1 hF2)
  refine ⟨c, hc, hcc, ?_⟩
  intro om oms ϖ μ U0 Φ hϖ hO hT hμ0 hμ hU0 hΦ0 hΦ
  exact h _ _ ϖ μ U0 Φ hϖ (omega_integral_criterion K0 K p ν σ j hU hj om oms hO hT) hμ0 hμ hU0 hΦ0 hΦ

theorem kernel_of_f : KernelOfF := by
  intro p _ K0 _ _ _ _ σ hU hζ F hF be hF1 hF2 K _ _ _ j ν r0 r1 _ hj hϖ om oms hO hT U0 Φ hU0 hΦ0
    hΦ TT colN hts hp I n
  obtain ⟨ϖ, hϖ⟩ := hϖ
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast j, hj]
    exact hU.2.2.1
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hU.1.ne_zero
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    apply hpK
    rw [← hϖ, zero_pow]
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hU.2.1.le 2
    omega
  obtain ⟨-, -, μ, hμ0, -, hμ, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.logRescale K p ϖ hU.1 hnp hϖ
  rw [theta_integer_is_theta_log K0 K p ν r0 r1 σ j om oms ϖ μ hU.1.two_le hϖ0 hμ0 hμ]
  exact Formalism.InvariantFactorPaths.G7.Top.kernel_from_k_one_k p K0 σ hU hζ F hF be (betaHypOfF K0 p σ hU F be hF1 hF2) K j
    ν r0 r1 hj _ _ ϖ μ U0 Φ hϖ (omega_integral_criterion K0 K p ν σ j hU hj om oms hO hT) hμ0 hμ hU0 hΦ0 hΦ
    TT colN hts hp I n

end Formalism.L2.Th1.D
