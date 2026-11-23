import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.CmDatumSmallPrimesLogBoundsOfParams
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONPage
import Development.AbelianVarietyTheory.Definitions.Jets.NotRunTiesZeroSteps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunWeightsSum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndexAssembly

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage GlobalTheory.RunDepth

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

def topDeg (Tp : ParamsT D L Pm) (hK : DV.KapDef D) : ℕ := (Finset.Icc 1 D.R.m).sup fun j => WeightAlgebra.DF (lR Tp hK j)

def SizeRows (Tp : ParamsT D L Pm) (hK : DV.KapDef D) : Prop :=
  L.etaSz * L.sc.b ^ ((4 : ℝ) / 5) ≤ L.sc.w'' D.R.n ∧ 11 ≤ L.sc.x ^ (L.sc.ez / 5) ∧
    2 * Real.pi * (Tp.nWn : ℝ) ≤ (topDeg Tp hK : ℝ) ^ 2 ∧ 10 ≤ Pm.CnW ∧
    L.sc.x ^ (-L.sc.eps) ≤ L.de2 ∧ L.de2 ≤ 1 / (4 * (D.host.Lw : ℝ)) ∧ (∀ i, (D.host.g i : ℝ) ≤ L.sc.b ^ 9) ∧
    Real.log ((D.host.q * D.host.d : ℕ) : ℝ) ≤ D.R.m ∧ (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b ∧ (D.R.N D.R.m : ℝ) ≤ L.sc.X' ∧
    44 ≤ D.R.m ∧ 0 ≤ (D.R.n : ℝ)

def DomPlus (Tp : ParamsT D L Pm) (hK : DV.KapDef D) : Prop :=
  (∀ j, InR D j → WeightAlgebra.DomAt D L j Tp.nWn Tp.CP) ∧ SizeRows Tp hK

theorem le_topDeg (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) : WeightAlgebra.DF (lR Tp hK j) ≤ topDeg Tp hK :=
  Finset.le_sup (f := fun j => WeightAlgebra.DF (lR Tp hK j)) (Finset.mem_Icc.2 hj)

theorem mul_DF_le (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) :
    Tp.TO * WeightAlgebra.DF (lR Tp hK j) ≤ WeightAlgebra.DF (kaR Tp hK j) := by
  obtain ⟨⟨-, h1, h2⟩, -⟩ := run_weights_sum D L Pm Tp hK j hj
  unfold WeightAlgebra.DF WeightAlgebra.degP
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => ?_)
  · have := h1 τ i
    zify
    omega
  · have := h2 τ i
    zify
    omega

theorem three_le_scale_of_pow_bound (h : 11 ≤ L.sc.x ^ (L.sc.ez / 5)) : 3 ≤ L.sc.x := by
  have := Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (show L.sc.ez / 5 ≤ 1 by linarith [L.sc.eps_lt, L.sc.ez_le])
  rw [Real.rpow_one] at this
  linarith

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _)

theorem one_le_PP (Tp : ParamsT D L Pm) : 1 ≤ Tp.PP := by
  have h : (40 : ℝ) ≤ Tp.nWn := by exact_mod_cast Tp.nW_40
  linarith [Tp.nW_le]

theorem sqrt_b_le (L : SizeData₂ D) : L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b := by
  have := Real.rpow_le_rpow_of_exponent_le (one_le_b L) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  rwa [Real.rpow_one] at this

theorem four_le_n (D : D7) : 4 ≤ D.R.n := D.host.four_le_n'

theorem cloud_le (Pm : ParameterChoice' D L) : L.sc.X' * (L.Sc + L.etaSz) ≤ L.sc.b := by
  have hx := L.sc.one_lt_alt
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hn : (4 : ℝ) ≤ D.R.n := by exact_mod_cast four_le_n D
  have hb := one_le_b L
  have hw : L.sc.X' * L.sc.w'' D.R.n = L.sc.b / D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a
    field_simp
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a
    positivity
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by have := D.R.m_add_three_le_k; omega)
  have h1 : L.Sc ≤ L.sc.w'' D.R.n := (le_mul_of_one_le_left L.Sc_pos.le hk).trans Pm.kS_le
  have h2 : L.etaSz ≤ L.sc.w'' D.R.n :=
    (le_mul_of_one_le_left L.etaSz_pos.le L.t_win.1).trans (Pm.teta.trans (div_le_self hw0 hx.le))
  have h3 : L.sc.b / D.R.n ≤ L.sc.b / 4 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hn
  nlinarith

theorem le_Lw (L : SizeData₂ D) : 22 ≤ D.host.Lw := by
  have h := L.logFiveDepth_le
  have h2 := L.weightLength_ge_depth
  rcases Nat.eq_zero_or_pos L.j0 with h0 | h0
  · exfalso
    rw [h0, Nat.cast_zero] at h
    have hn : (4 : ℝ) ≤ D.R.n := by exact_mod_cast four_le_n D
    have hm : (0 : ℝ) < D.R.m := by exact_mod_cast lt_of_lt_of_le two_pos D.R.two_le_m
    have hN : (D.R.m : ℝ) ≤ D.R.N D.R.m := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (show D.R.m ≤ D.R.N D.R.m by unfold Ranks.N; omega)
    refine absurd h (not_le.2 (Real.logb_pos (by norm_num) ?_))
    rw [lt_div_iff₀ hm]
    nlinarith
  · omega

section Obj

variable {T : Core D} {EX : ErrX D} {Tp : ParamsT D L Pm} {hK : DV.KapDef D} [StarRing (𝓞 D.host.E)]
  {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
  {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

variable (Tp hK) in

def NumTie (O : OnObj S P c) : Prop :=
  O.rr = (D.R.r : ℝ) ∧ O.T2 = D.host.T2.card ∧ O.Nc = budgetNc D.R L.sc.x L.sc.eps D.host.T2.card ∧
    O.DF = (topDeg Tp hK : ℝ) ∧ O.de2 = L.de2 ∧ O.pde = D.host.pde

variable {O : OnObj S P c} {ι : Bs.J → ℕ}

theorem pageLeaves (h : RunTie T EX Tp hK O ι) (hN : NumTie Tp hK O) (hR : SizeRows Tp hK) : PageLeaves O 1 := by
  obtain ⟨nr, nT2, nNc, nDF, -, -⟩ := hN
  obtain ⟨r1, r2, r3, -, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hR
  have hx := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have eb : O.b = L.sc.b := Model.b_eq h
  have eL : O.L = L.sc.L := by rw [L_eq_rpow, h.x_eq, h.eps_eq]; rfl
  have en : nH O = D.R.n := by unfold nH; rw [h.f_eq]; unfold Ranks.f; push_cast; ring
  have eX : Xp O = L.sc.X' := by unfold Xp; rw [h.x_eq, h.eps_eq]; rfl
  have ea : aa O = L.sc.a := by unfold aa; rw [h.x_eq, eb]; rfl
  have ew : wpp O = L.sc.w'' D.R.n := by unfold wpp; rw [ea, eX, en, h.x_eq]; rfl
  have ed : dl2 O = L.de2 := by unfold dl2; rw [nT2, en, L.typeDensity_eq_card_div]
  have hb := one_le_b L
  have hn : (4 : ℝ) ≤ D.R.n := by exact_mod_cast four_le_n D
  have hPP := one_le_PP Tp
  have hT : (1 : ℝ) ≤ Tp.TO := by exact_mod_cast TO_pos Tp
  have hmk := D.R.m_add_three_le_k
  have hr : (9 : ℝ) ≤ D.R.r := by exact_mod_cast (show 9 ≤ D.R.r by unfold Ranks.r; omega)
  have hf : (1 : ℝ) ≤ D.R.f := by have := four_le_n D; exact_mod_cast (show 1 ≤ D.R.f by unfold Ranks.f; omega)
  have hL : 10 ≤ L.sc.L := le_trans (by linarith) (Real.rpow_le_rpow_of_exponent_le hx.le
    (show L.sc.ez / 5 ≤ L.sc.eps by linarith [L.sc.ez_pos, L.sc.ez_le]))
  have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hc := cloud_le Pm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ExponentSmallBound; rw [h.eps_eq]; exact ⟨L.sc.eps_pos, L.sc.eps_lt⟩
  · unfold HalfDegreeAtLeastFour; rw [en]; exact hn
  · unfold PrimeCongruenceConditions; rw [h.cmQuadraticForm_eq_alternatingForm, h.dd_eq]; exact ⟨D.host.hyp.1, D.host.hyp.2.1, D.host.hyp.2.2.1, D.host.hyp.2.2.2.1⟩
  · unfold DegreeAtLeastFortyFour; rw [en, h.m_eq]; exact ⟨by exact_mod_cast r11, r12⟩
  · unfold DimensionExceedsDegreeByThree; rw [h.m_eq, h.k_eq]; exact_mod_cast hmk
  · unfold RankAndLengthLowerBounds; rw [nr, eL]; exact ⟨hr, hL⟩
  · unfold LeafSZ1; rw [h.T_eq, eb]
    exact ⟨by linarith, (le_mul_of_one_le_right (by linarith) hPP).trans (Tp.TO_PP'.trans (sqrt_b_le L))⟩
  · refine ⟨D.R.f, h.f_eq.symm, fun j => ⟨fun _ => 2 * L.sc.b, ?_, fun _ => ⟨by linarith, by rw [eb]⟩⟩⟩
    rw [h.wt_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · unfold SupportGapBounds; rw [ew, eX, eb, h.k_eq, h.Sc_eq, h.eta_eq]; exact ⟨Pm.kS_le, hc⟩
  · unfold EtaPowerBound; rw [ew, eb, h.eta_eq]; exact r1
  · unfold LeafSign; rw [h.Sc_eq, h.eta_eq]; exact ⟨L.Sc_pos.le, L.etaSz_pos.le⟩
  · refine ⟨D.R.t, Nat.cast_nonneg _, ?_⟩
    rw [eX, h.k_eq, h.m_eq]
    unfold Ranks.N at r10
    push_cast at r10
    exact r10
  · unfold LogPrimeProductBound; rw [h.cmQuadraticForm_eq_alternatingForm, h.dd_eq, h.m_eq]; exact r8
  · unfold ProductWithRatioBound; rw [h.k_eq, h.bp_eq, eb]; exact r9
  · unfold ConductorCongruentPrimePair; rw [h.jets_eq_fact, h.g2_eq, h.cmQuadraticForm_eq_alternatingForm, h.dd_eq, h.sm_eq, eb]
    exact ⟨D.host.g_prime 0, D.host.g_prime 1, r7 0, r7 1, D.host.g_ne, D.host.condN,
      ⟨D.host.q_dvd_condN, D.host.d_dvd_condN, fun p hp => ⟨(D.host.mem_small_iff.1 hp).1.one_lt,
        (D.host.mem_small_iff.1 hp).2.trans D.host.QS_dvd_condN⟩⟩, Pm.g_mod 0, Pm.g_mod 1⟩
  · exact ⟨Tp.PP, hPP, by rw [h.T_eq, eb]; exact Tp.precision_cube_order_sq_le_sqrt.trans (sqrt_b_le L)⟩
  · unfold PowerTwelveBound; rw [h.f_eq, nr, eL, eb]
    have hZ : 1 ≤ zBase L := by
      unfold zBase
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf (by linarith)) (by linarith)
    have h1 : zBase L ^ 12 ≤ zBase L ^ Tp.eP := by
      have := Real.rpow_le_rpow_of_exponent_le hZ Tp.eP_ge
      rwa [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have h2 : zBase L ^ Tp.eP ≤ Tp.PP := by
      rw [Tp.PP_eq]; exact le_mul_of_one_le_left (by positivity) Tp.one_le_CP
    exact h1.trans (h2.trans ((le_mul_of_one_le_left (by linarith) hT).trans (Tp.TO_PP'.trans (sqrt_b_le L))))
  · unfold DiscriminantDegreeBound; rw [nDF]; exact ⟨Nat.cast_nonneg _, Tp.nWn, by exact_mod_cast Tp.nW_40, r3⟩
  · have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (show 0 < D.R.m by omega)
    have hD : 1 ≤ Tp.Dp := by
      rw [Tp.Dp_eq]
      exact Nat.mul_pos (by exact_mod_cast hf) (Nat.choose_pos (by unfold Ranks.r; omega))
    refine ⟨Tp.PP, Tp.Dp, hPP, by exact_mod_cast hD, ?_⟩
    rw [ed, h.k_eq, h.f_eq, h.x_eq, h.T_eq, h.m_eq, mul_assoc (Tp.TO : ℝ)]
    have h1 := (div_le_iff₀ (mul_pos hm L.thickDensity_pos)).1 Tp.TO_ge
    have h2 : L.sc.x ≤ L.sc.x ^ Tp.Cp := by
      have := Real.rpow_le_rpow_of_exponent_le hx.le Tp.Cp_ge
      rwa [Real.rpow_one] at this
    exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans h1
  · unfold TwistDensityBounds; rw [ed, h.x_eq, h.eps_eq]; exact ⟨r5, D.host.Lw, by exact_mod_cast le_Lw L, r6⟩
  · unfold TimeDiscriminantBound; rw [nDF, h.T_eq, h.k_eq, h.f_eq, eb]
    obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup (Finset.Icc 1 D.R.m) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
      fun j => WeightAlgebra.DF (lR Tp hK j)
    have hj' : InR D j := Finset.mem_Icc.1 hj
    have h1 : (Tp.TO : ℝ) * topDeg Tp hK ≤ WeightAlgebra.DF (kaR Tp hK j) := by
      unfold topDeg; rw [e]; exact_mod_cast mul_DF_le Tp hK hj'
    have h2 := (DF_kaR_le D L Pm Tp hK (three_le_scale_of_pow_bound r2) r9 j hj').1
    have h3 : L.Sc + L.etaSz ≤ L.sc.b :=
      (le_mul_of_one_le_left (add_pos L.Sc_pos L.etaSz_pos).le hX1).trans hc
    refine h1.trans (h2.trans ?_)
    calc _ ≤ (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * L.sc.b) := by gcongr
      _ = _ := by ring
  · unfold TieVd; rw [h.vd_eq, h.sm_eq, h.cmQuadraticForm_eq_alternatingForm, h.dd_eq, eL]
    exact ⟨Real.logb_nonneg (by norm_num) (by exact_mod_cast D.host.QS_pos), (UpperTheory.cmDatum_smallPrimes_log_bounds_of_params D L Pm).1,
      D.host.q_notMem_small, D.host.d_notMem_small⟩
  · unfold SecondRatioDefinition; rw [ea, ew, h.depthNumbers_threshold_eq]; rfl
  · unfold TieBp; rw [ea, eX, h.bp_eq]; rfl
  · unfold TieNc; rw [nNc, ed, en, eb, h.k_eq, h.x_eq, h.eps_eq, L.typeDensity_eq_card_div, two_mul, Real.rpow_add hx0]
    unfold budgetNc rankBudget
    rw [Real.rpow_neg hx0.le]
    have := Real.rpow_pos_of_pos hx0 L.sc.eps
    change _ * _ * L.sc.b * _ / _ = _
    field_simp

theorem leafX (h : RunTie T EX Tp hK O ι) (hN : NumTie Tp hK O) (hR : SizeRows Tp hK) : LeafX O := by
  have r9 := hR.2.2.2.2.2.2.2.2.1
  have hx := L.sc.one_lt_alt
  have hb := one_le_b L
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by have := D.R.m_add_three_le_k; omega)
  have hn : (4 : ℝ) ≤ D.R.n := by exact_mod_cast four_le_n D
  constructor
  · unfold OnObj.xe
    rw [h.x_eq, h.eps_eq]
    have h0 : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a; positivity
    have h1 : L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.b := (le_mul_of_one_le_left h0 hk).trans r9
    rw [div_le_iff₀ hX, mul_comm L.sc.b] at h1
    refine ((Real.log_le_iff_le_exp (by linarith)).2 (le_of_mul_le_mul_right h1 (by linarith))).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith [L.sc.eps_pos])
  · have h1 := L.thickDensity_le_one
    rw [L.typeDensity_eq_card_div, div_le_one (by linarith)] at h1
    rw [hN.2.1, h.f_eq]
    unfold Ranks.f
    push_cast
    linarith

theorem numericLeaves (h : RunTie T EX Tp hK O ι) (hN : NumTie Tp hK O) (hR : SizeRows Tp hK) (hC : ConstC c)
    (hB : ConstBad c) (hx : 3 * c.C ≤ L.sc.x) : LeafPage O ∧ LeafSizes O ∧ LeafX O ∧ LeafBad O := by
  obtain ⟨h02, h11, h12, h1246, h29, h21, h1, hW, h14, h011, hSg, h1243, h121, h1232, h75, h19, h18, h13, h231, h44, hZ3,
    tVd, tX2, tBp, tNc⟩ := pageLeaves h hN hR
  have hx3 : 3 ≤ O.x := h.x_eq ▸ three_le_scale_of_pow_bound hR.2.1
  have hC' : 1 ≤ c.C := hC
  exact ⟨leafPage_of O hC hx3 h11 h12 h1246 h29 h1 hSg h75 tVd tBp tNc,
    leafSizes_of_page O 1 zero_le_one hC' hx3 (by rw [mul_one, h.x_eq]; exact hx) h02 h11 h1246 h29 h21 hW h14 h011 hSg h1243
      h13 h231 h44 tX2 hZ3,
    leafX h hN hR,
    leafBad_of_page O (by linarith) hB.1 hB.2 hx3 h02 h11 h1246 h21 h1 hW h14 h121 h1232 h75 h19 h18 tVd⟩

end Obj

end GlobalTheory.IndexAssembly
