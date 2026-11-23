import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVN
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVL
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
import Formalism.FlagUnipotentLattices.ArithmeticIdentityEntries
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace Formalism.MainNotions.BridgeLemV

open NumberField Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem std_form_eq (n : ℕ) : Formalism.MainNotions.StandardLattice.stdForm K n = stdForm K n := rfl

theorem std_lattice_eq (n : ℕ) : Formalism.MainNotions.StandardLattice.stdLat K n = stdLat K n := rfl

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem mass_two_eq (hK : IsCMUnram K) :
    mass (Formalism.MainNotions.StandardLattice.stdForm K 2) (Formalism.MainNotions.StandardLattice.stdLat K 2) =
      mass (Formalism.MainNotions.StandardLattice.stdForm K 1) (Formalism.MainNotions.StandardLattice.stdLat K 1) * massRatioRightSide K 2 := by
  rw [std_form_eq, std_form_eq, std_lattice_eq, std_lattice_eq]
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, -, hall⟩ := massConst_all hermRepUnram liStat hK hF
  have mk : ∀ n : ℕ, 1 ≤ n →
      mass (stdForm K n) (stdLat K n) = c₁ * ∏ j ∈ Finset.Icc 2 n, massRatioRightSide K j := by
    intro n hn
    have hs := stdForm_isSymm K n
    have ho := stdLat_isOrtho K n
    have := finiteDimensional_of_ortho ho
    have e := hall n hn _ (stdForm K n) (stdLat K n) hs (isTotPosDef_of_ortho hK hs ho)
      (finrank_of_ortho ho) (isLattice_of_ortho ho) (isIntegralLat_of_ortho ho)
    rw [lamG_eq_one_of_ortho hK hF hs ho, mul_one] at e
    exact e
  rw [mk 2 (by norm_num), mk 1 le_rfl, Finset.Icc_self, Finset.prod_singleton,
    Finset.Icc_eq_empty (by norm_num), Finset.prod_empty, mul_one]

theorem classNumber_le (hK : IsCMUnram K) :
    (classNumber K : ℝ) ≤ (2 * vInv K) ^ fDeg K * (1 + (fDeg K : ℝ) * Real.log (2 * vInv K)) ^ (2 * fDeg K) := by
  have hc := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.classNumberBound K (fun w => hK.1.isComplex w)
  have hsq : Real.sqrt |(discr K : ℝ)| = (2 * vInv K) ^ fDeg K := by
    obtain ⟨h1, -, h3⟩ := discrTower K (cmF K) hK (Formalism.MainNotions.BridgeLemVN.fixF K)
    rw [h1, Real.sqrt_sq_eq_abs, h3, abs_of_nonneg (pow_nonneg (by linarith [vInv_pos K]) _)]
  rw [hsq, finrank_eq_two_fDeg hK, Real.log_pow] at hc
  exact hc

def boundTwo (E : Type) [Field E] [NumberField E] : ℝ :=
  2 ^ fDeg E * (2 * vInv E) ^ fDeg E * (1 + (fDeg E : ℝ) * Real.log (2 * vInv E)) ^ (2 * fDeg E) *
    ((vInv E / Real.pi) ^ 2) ^ fDeg E * Real.exp (2 * Real.pi ^ 2 * fDeg E / 3)

def MassTwoBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], IsCMUnram E →
    mass (Formalism.MainNotions.StandardLattice.stdForm E 2) (Formalism.MainNotions.StandardLattice.stdLat E 2) ≤ boundTwo E

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem MassTwoBound_holds : MassTwoBound := by
  intro E _ _ _ hE
  rw [mass_two_eq hE]
  have h1 : mass (Formalism.MainNotions.StandardLattice.stdForm E 1) (Formalism.MainNotions.StandardLattice.stdLat E 1) ≤
      ((classNumber E * 2 ^ fDeg E : ℕ) : ℝ) := by
    rw [std_form_eq, std_lattice_eq]; exact Formalism.MainNotions.BridgeLemVN.mass_std_one_le hE
  have hc := classNumber_le hE
  have hv0 : 0 ≤ vInv E := (vInv_pos E).le
  have hA0 : 0 ≤ (2 * vInv E) ^ fDeg E * (1 + (fDeg E : ℝ) * Real.log (2 * vInv E)) ^ (2 * fDeg E) :=
    le_trans (Nat.cast_nonneg _) hc
  have hA : mass (Formalism.MainNotions.StandardLattice.stdForm E 1) (Formalism.MainNotions.StandardLattice.stdLat E 1) ≤
      (2 * vInv E) ^ fDeg E * (1 + (fDeg E : ℝ) * Real.log (2 * vInv E)) ^ (2 * fDeg E) * 2 ^ fDeg E := by
    refine h1.trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hZ : Real.exp (2 * ((Module.finrank ℚ E : ℝ) * Formalism.MainNotions.BridgeLemVL.Z2)) =
      Real.exp (2 * Real.pi ^ 2 * fDeg E / 3) := by
    rw [Formalism.MainNotions.BridgeLemVL.zeta_two_eq_pi_sq_div_six, finrank_eq_two_fDeg hE]
    congr 1
    push_cast
    ring
  have hB := (Formalism.MainNotions.BridgeLemVL.mass_ratio_rank_two_le hE).trans (le_of_eq (by rw [hZ]))
  calc mass (Formalism.MainNotions.StandardLattice.stdForm E 1) (Formalism.MainNotions.StandardLattice.stdLat E 1) * massRatioRightSide E 2
      ≤ ((2 * vInv E) ^ fDeg E * (1 + (fDeg E : ℝ) * Real.log (2 * vInv E)) ^ (2 * fDeg E) * 2 ^ fDeg E) *
          (((vInv E / Real.pi) ^ 2) ^ fDeg E * Real.exp (2 * Real.pi ^ 2 * fDeg E / 3)) :=
        mul_le_mul hA hB (massRatio_pos hE 2 le_rfl).le (by positivity)
    _ = boundTwo E := by unfold boundTwo; ring

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem mass_two_le_pow (hK : IsCMUnram K) {Y : ℝ} (hY : 2 ≤ Y) (hv : 2 * vInv K ≤ Y)
    (hf : (fDeg K : ℝ) ≤ Y) :
    mass (Formalism.MainNotions.StandardLattice.stdForm K 2) (Formalism.MainNotions.StandardLattice.stdLat K 2) ≤ Y ^ (22 * fDeg K) := by
  refine (MassTwoBound_holds K hK).trans ?_
  unfold boundTwo
  have hv0 : 0 ≤ vInv K := (vInv_pos K).le
  have hr1 : 1 ≤ 2 * vInv K := Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv
  have hY0 : 0 ≤ Y := by linarith
  have hf0 : (0 : ℝ) ≤ fDeg K := Nat.cast_nonneg _
  have p1 : (2 : ℝ) ^ fDeg K ≤ Y ^ fDeg K := pow_le_pow_left₀ (by norm_num) hY _
  have p2 : (2 * vInv K) ^ fDeg K ≤ Y ^ fDeg K := pow_le_pow_left₀ (by linarith) hv _
  have hl0 : 0 ≤ Real.log (2 * vInv K) := Real.log_nonneg hr1
  have hl : Real.log (2 * vInv K) ≤ 2 * vInv K :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hL : 1 + (fDeg K : ℝ) * Real.log (2 * vInv K) ≤ Y ^ 3 := by
    have h1 : (fDeg K : ℝ) * Real.log (2 * vInv K) ≤ Y * Y := mul_le_mul hf (hl.trans hv) hl0 hY0
    nlinarith
  have hL0 : 0 ≤ 1 + (fDeg K : ℝ) * Real.log (2 * vInv K) := by positivity
  have p3 : (1 + (fDeg K : ℝ) * Real.log (2 * vInv K)) ^ (2 * fDeg K) ≤ (Y ^ 3) ^ (2 * fDeg K) :=
    pow_le_pow_left₀ hL0 hL _
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hq0 : 0 ≤ vInv K / Real.pi := div_nonneg hv0 (by linarith)
  have hq : vInv K / Real.pi ≤ Y := (div_le_self hv0 hpi).trans (by linarith)
  have p4 : ((vInv K / Real.pi) ^ 2) ^ fDeg K ≤ (Y ^ 2) ^ fDeg K :=
    pow_le_pow_left₀ (pow_nonneg hq0 2) (pow_le_pow_left₀ hq0 hq 2) _
  have he8 : Real.exp 8 ≤ 2 ^ 12 := by
    have e : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc Real.exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 8
      _ ≤ 2 ^ 12 := by norm_num
  have p5 : Real.exp (2 * Real.pi ^ 2 * fDeg K / 3) ≤ (Y ^ 12) ^ fDeg K := by
    have hpi2 : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    calc Real.exp (2 * Real.pi ^ 2 * fDeg K / 3) ≤ Real.exp ((fDeg K : ℕ) * 8) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ = Real.exp 8 ^ fDeg K := Real.exp_nat_mul 8 _
      _ ≤ (2 ^ 12) ^ fDeg K := pow_le_pow_left₀ (Real.exp_pos 8).le he8 _
      _ ≤ (Y ^ 12) ^ fDeg K := pow_le_pow_left₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) hY 12) _
  have q1 := mul_le_mul p1 p2 (pow_nonneg (by linarith) _) (pow_nonneg hY0 _)
  have q2 := mul_le_mul q1 p3 (pow_nonneg hL0 _) (mul_nonneg (pow_nonneg hY0 _) (pow_nonneg hY0 _))
  have q3 := mul_le_mul q2 p4 (pow_nonneg (pow_nonneg hq0 2) _)
    (mul_nonneg (mul_nonneg (pow_nonneg hY0 _) (pow_nonneg hY0 _)) (pow_nonneg (pow_nonneg hY0 3) _))
  have q4 := mul_le_mul q3 p5 (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hY0 _) (pow_nonneg hY0 _))
      (pow_nonneg (pow_nonneg hY0 3) _)) (pow_nonneg (pow_nonneg hY0 2) _))
  refine q4.trans (le_of_eq ?_)
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

end Formalism.MainNotions.BridgeLemV

end
