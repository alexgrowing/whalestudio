import Formalism.SizeWindowBrackets.ChainSlopeWindows.PrimeCongruenceConditions
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AnalyticFirstToLatticeDiscriminant
import Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealIntegralFormula
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpNegLeDivPowFour
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.SmallPrimeFactorSumBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.PsiZeroIntegral
import Formalism.GL3MeanSquares.HookFormulaTorsion.HasDerivAtLogSquareAntiderivative
import Formalism.GL3MeanSquares.HookFormulaTorsion.ShortIntervalImpliesProgressionsStatement
import Formalism.GL3MeanSquares.HookFormulaTorsion.SizeEstimates
import Formalism.GL3MeanSquares.ZeroFreeRegionGl2PrimeChoiceResults
import Formalism.GL3MeanSquares.HookFormulaTorsion.CongruenceSubgroupTorsionFree
import Formalism.GL3MeanSquares.HookFormulaTorsion.NoExceptionalOfNoRealZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimePairOfBoxAndWeakMeanSquareHypotheses
import Formalism.GL3MeanSquares.HookFormulaTorsion.BoxCountOfZeroDensity
import Formalism.LocalToGlobal.GlobalTheory.GL2.Statement

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.MergeGL2

open Formalism.LFunctionChainParameters Formalism.HermitianLattices

theorem tw_eq : @LBr2.tw = @ZeroFreeRegionGL2.tw := rfl
theorem prop_2_5_eq : @LBr2.ExistsSplitGoodPrimePair = @ZeroFreeRegionGL2.ExistsSplitGoodPrimePair := rfl
theorem LogNE_eq : LBr2.LogNE = ZeroFreeRegionGL2.LogNE := rfl
theorem NoRealZeroSmall_eq : LBr2.NoRealZeroSmall = GL2b2.NoRealZeroSmall := rfl

theorem noRealZeroSmall : LBr2.NoRealZeroSmall := NoRealZeroSmall_eq ▸ GL2b2.no_real_zero_small_modulus

theorem chi8NoRealZero : LChain6.Chi8NoRealZero := noRealZeroSmall.2

theorem logNE : LBr2.LogNE := LogNE_eq ▸ ZeroFreeRegionGL2.log_nonexceptional_bound

theorem hostAnalyticConcl : LBr2.HostAnalyticConcl := LBr2.analytic_input_conditional noRealZeroSmall logNE

theorem hostAn : ∃ c' : ℝ, 0 < c' ∧ LChain6.HostAn c' := hostAnalyticConcl

theorem chain6At :
    ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
      ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → LChain6.Chain6Core A Cord eD eL K cHH eK CL eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε) :=
  LChain6.chain_analytic_at_point chi8NoRealZero

def EndFor (c' ε A C x : ℝ) (q d : ℕ) [Fact q.Prime] [Fact d.Prime] : Prop :=
  LBr2.PrimePairBounds ε C x q d ∧ Formalism.FrobeniusOrbits.HostHyp q d ∧ ∀ e : ℕ, ((2 ^ e : ℕ) : ℝ) ≤ x ^ A →
    ThickSetMeanBounds.ThinScales (LHost.hostData e q d) (LChain2.hostEll e q d) (Real.exp (x ^ (ε / 3)))
      (Real.exp (-c' * x ^ (ε / 8))) ∧
    ThickSetMeanBounds.ValuesAtX (LHost.hostData e q d) (LChain2.hostEll e q d) x ε C

def AnalyticEndW : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₂ C₂' x₂ C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₂ → 0 < C₄ →
    ZeroFreeRegionGL2.BoxCountHyp C₂ → ZeroFreeRegionGL2.BoxTailHyp ε C₂' x₂ → WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ (q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime), EndFor c' ε A C₂' x q d

def AnalyticEnd : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₂ C₂' x₂ C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₂ → 0 < C₄ →
    ZeroFreeRegionGL2.BoxCountHyp C₂ → ZeroFreeRegionGL2.BoxTailHyp ε C₂' x₂ → ZeroFreeRegionGL2.MeanSquareHyp ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ (q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime), EndFor c' ε A C₂' x q d

def AnalyticEndSel : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₂ C₂' x₂ C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₂ → 0 < C₄ →
    ZeroFreeRegionGL2.BoxCountHyp C₂ → ZeroFreeRegionGL2.BoxTailHyp ε C₂' x₂ → WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε C₂' x ∧
      ∃ (_ : Fact (FiltrationCocycleLiftCriterion.qSel ε C₂' x).Prime) (_ : Fact (FiltrationCocycleLiftCriterion.dSel ε C₂' x).Prime),
        EndFor c' ε A C₂' x (FiltrationCocycleLiftCriterion.qSel ε C₂' x) (FiltrationCocycleLiftCriterion.dSel ε C₂' x)

def AnalyticEndTied : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₂ C₂' x₂ C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₂ → 0 < C₄ →
    ZeroFreeRegionGL2.BoxCountHyp C₂ → ZeroFreeRegionGL2.BoxTailHyp ε C₂' x₂ → WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε C₂' →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A C₂' x D.host.q D.host.d

def CVal0 : ℝ := 1200 * (Real.log 4 + 4) + 1

def q1At (ε x : ℝ) : ℕ := FiltrationCocycleLiftCriterion.qSel ε CVal0 x

def dAt (ε x : ℝ) : ℕ := FiltrationCocycleLiftCriterion.dSel ε CVal0 x

def AnalyticEndClosed : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₄ →
    ZeroDensityInBoxes.ZeroDensityBox → WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x)

def AnalyticEndClosedTied : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₄ →
    ZeroDensityInBoxes.ZeroDensityBox → WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d

section LatticeGramTransferCondition

open Formalism Formalism.D5 Formalism.HN Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6

def CoreAt (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A Cord eD eL K cHH eK eW KW ε x : ℝ) : Prop :=
  ∃ (e : ℕ) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ o u0, FamC (W o u0) m) (Rw : ∀ o u0, Rows (Fc o u0).toFam) (O : ∀ o, SizeCountLevelObjects (HA e) (W o) m TT)
    (Lp : HA e → Ω → LossP (HA e) m)
    (P : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ (∀ o, (O o).Sc = P.Sc) ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHyp (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun o u0 => (Fc o u0).toFam) Lp P π s sB
      BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      Inputs6d (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 (a o) (w o) (Fc o) (Rw o) (O o) η eK K logOm
        C0 cZ cL cE5 c5 C0S κ off (btH o) g₁ g₂

def Chain6AtClosed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε C₄ x₄ : ℝ, 0 < ε → ε < 1 / 4 → 0 < A → 0 < C₄ →
    ZeroDensityInBoxes.ZeroDensityBox → WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

end LatticeGramTransferCondition

theorem analytic_conclusion_of_prop_2_5 {c' : ℝ} (h : LChain6.HostAn c') (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (C : ℝ) (q d : ℕ) [Fact q.Prime] [Fact d.Prime],
      LBr2.PrimePairBounds ε C x q d → EndFor c' ε A C x q d := by
  obtain ⟨x₀, hx₀⟩ := h ε A hε hA
  exact ⟨x₀, fun x hx C q d _ _ hP => ⟨hP, (hx₀ x hx C q d hP).1, (hx₀ x hx C q d hP).2⟩⟩

theorem sel_spec {ε C x : ℝ} (h : FiltrationCocycleLiftCriterion.QDExists ε C x) : FiltrationCocycleLiftCriterion.QDGood ε C x (FiltrationCocycleLiftCriterion.qSel ε C x) (FiltrationCocycleLiftCriterion.dSel ε C x) := by
  classical
  have h' : ∃ q : ℕ, ∃ d : ℕ, FiltrationCocycleLiftCriterion.QDGood ε C x q d := h
  have hq : ∃ d : ℕ, FiltrationCocycleLiftCriterion.QDGood ε C x (FiltrationCocycleLiftCriterion.qSel ε C x) d := by
    unfold FiltrationCocycleLiftCriterion.qSel
    rw [dif_pos h']
    exact Nat.find_spec h'
  unfold FiltrationCocycleLiftCriterion.dSel
  rw [dif_pos hq]
  exact Nat.find_spec hq

theorem analyticEndSel : AnalyticEndSel := by
  obtain ⟨c', hc', hH⟩ := hostAn
  refine ⟨c', hc', fun ε A C₂ C₂' x₂ C₄ x₄ hε hε1 hA hC₂ hC₄ h1 h2 h3 => ?_⟩
  obtain ⟨xa, hxa⟩ := WeakMeanSquareEstimates.prime_pair_of_box_and_weak_mean_square_hypotheses ε C₂ C₂' x₂ C₄ x₄ hε hε1 hC₂ hC₄ h1 h2 h3
  obtain ⟨xb, hxb⟩ := analytic_conclusion_of_prop_2_5 hH ε A hε hA
  refine ⟨max xa xb, fun x hx => ?_⟩
  have hP : LBr2.ExistsSplitGoodPrimePair ε C₂' x := prop_2_5_eq ▸ hxa x (le_trans (le_max_left _ _) hx)
  obtain ⟨q, d, iq, id, hqd⟩ := (LBr2.proposition_at_iff ε C₂' x).1 hP
  have hE : FiltrationCocycleLiftCriterion.QDExists ε C₂' x := ⟨q, d, iq, id, hqd⟩
  obtain ⟨jq, jd, hsel⟩ := sel_spec hE
  exact ⟨hE, jq, jd, hxb x (le_trans (le_max_right _ _) hx) C₂' _ _ hsel⟩

theorem analyticEndTied : AnalyticEndTied := by
  obtain ⟨c', hc', h⟩ := analyticEndSel
  refine ⟨c', hc', fun ε A C₂ C₂' x₂ C₄ x₄ hε hε1 hA hC₂ hC₄ h1 h2 h3 => ?_⟩
  obtain ⟨x₀, hx₀⟩ := h ε A C₂ C₂' x₂ C₄ x₄ hε hε1 hA hC₂ hC₄ h1 h2 h3
  refine ⟨x₀, fun x hx D hD => ?_⟩
  have key : ∀ q d : ℕ, q = FiltrationCocycleLiftCriterion.qSel ε C₂' x → d = FiltrationCocycleLiftCriterion.dSel ε C₂' x →
      ∃ (_ : Fact q.Prime) (_ : Fact d.Prime), EndFor c' ε A C₂' x q d := by
    intro q d hq hd
    subst hq hd
    exact (hx₀ x hx).2
  exact key _ _ hD.1 hD.2

theorem rpow_quarter_nonneg (Q : ℝ) : 0 ≤ Q ^ (1 / 4 : ℝ) := by
  rcases le_or_gt 0 Q with hQ | hQ
  · exact Real.rpow_nonneg hQ _
  · rw [Real.rpow_def_of_neg hQ]
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]

theorem boxCount_mono {C C' : ℝ} (hC : C ≤ C') (h : ZeroFreeRegionGL2.BoxCountHyp C) : ZeroFreeRegionGL2.BoxCountHyp C' := by
  intro t _ θ Q S hθ hθ2 hS
  exact le_trans (h t θ Q S hθ hθ2 hS) (mul_le_mul_of_nonneg_right hC (rpow_quarter_nonneg Q))

theorem boxCount_of_density (h : ZeroDensityInBoxes.ZeroDensityBox) : ∃ C : ℝ, 0 < C ∧ ZeroFreeRegionGL2.BoxCountHyp C := by
  obtain ⟨C, hC⟩ := ZeroDensityInBoxes.box_count_of_zero_density h
  exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), boxCount_mono (le_max_left _ _) hC⟩

open ArithmeticFunction Finset in

theorem mertens3 (y : ℝ) (hy : 2 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ 3 * (Real.log 4 + 4) * Real.log y := by
  have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  have hfl : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  obtain ⟨N, hN⟩ : ∃ N, ⌊y⌋₊ = N + 1 := ⟨⌊y⌋₊ - 1, by omega⟩
  have hNy : (N : ℝ) + 1 ≤ y := by
    have := Nat.floor_le (show (0 : ℝ) ≤ y by linarith)
    rw [hN] at this
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [hN]
  have h1 := Ext.BoxTail.tail_mertens_nat N
  have h2 := Ext.BoxTail.tail_mertens_psi (N + 1)
  push_cast at h2
  have h3 : (∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ)) / ((N : ℝ) + 1) ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hN0]
    exact h2
  have h4 : Real.log ((N : ℝ) + 1) ≤ Real.log y := Real.log_le_log hN0 hNy
  have h5 : (1 : ℝ) / 2 ≤ Real.log y := by
    have := Real.log_two_gt_d9
    have h6 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hC, mul_le_mul_of_nonneg_left h5 hC]

open ArithmeticFunction Finset in

theorem boxTail_CVal0_of {ε C x₀ : ℝ} (hε1 : ε ≤ 1) (h : ZeroFreeRegionGL2.BoxTailHyp ε C x₀) :
    ZeroFreeRegionGL2.BoxTailHyp ε CVal0 (max x₀ 3) := by
  intro x Q N _ χ hx hQlo hQhi hχ hgood
  obtain ⟨hfirst, _⟩ := h x Q N χ (le_trans (le_max_left _ _) hx) hQlo hQhi hχ hgood
  refine ⟨hfirst, ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  set z : ℝ := x ^ 400 with hz
  set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP
  have htail : ZeroFreeRegionGL2.tailL χ z = -ZeroFreeRegionGL2.logDerivLAtOne χ - P := rfl
  have hz2 : 2 ≤ z := by
    have : (3 : ℝ) ≤ z := by
      rw [hz]
      calc (3 : ℝ) ≤ x := hx3
        _ ≤ x ^ 400 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hPle : ‖P‖ ≤ 3 * (Real.log 4 + 4) * Real.log z := by
    refine le_trans (norm_sum_le _ _) (le_trans ?_ (mertens3 z hz2))
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχn : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    gcongr
    calc (Λ n : ℝ) * ‖χ (n : ZMod N)‖ ≤ (Λ n : ℝ) * 1 := by gcongr
      _ = Λ n := mul_one _
  have hlogz : Real.log z = 400 * Real.log x := by
    rw [hz, Real.log_pow]; norm_num
  have htail1 : ‖-ZeroFreeRegionGL2.logDerivLAtOne χ - P‖ ≤ 1 := by
    have h2 : x * ‖-ZeroFreeRegionGL2.logDerivLAtOne χ - P‖ ≤ x ^ ε := by
      have := hfirst
      rw [htail, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at this
      exact this
    have h3 : x ^ ε ≤ x := by
      calc x ^ ε ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hε1
        _ = x := Real.rpow_one x
    have h4 : x * ‖-ZeroFreeRegionGL2.logDerivLAtOne χ - P‖ ≤ x * 1 := by linarith
    exact le_of_mul_le_mul_left h4 hx0
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  rw [← norm_neg]
  calc ‖-ZeroFreeRegionGL2.logDerivLAtOne χ‖ = ‖P + (-ZeroFreeRegionGL2.logDerivLAtOne χ - P)‖ := by ring_nf
    _ ≤ ‖P‖ + ‖-ZeroFreeRegionGL2.logDerivLAtOne χ - P‖ := norm_add_le _ _
    _ ≤ 3 * (Real.log 4 + 4) * (400 * Real.log x) + 1 := by rw [← hlogz]; linarith
    _ ≤ CVal0 * Real.log x := by unfold CVal0; nlinarith

theorem boxTail_CVal0 (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) : ∃ x₂ : ℝ, ZeroFreeRegionGL2.BoxTailHyp ε CVal0 x₂ := by
  obtain ⟨C, x₀, h⟩ := ZeroDensityInBoxes.box_tail_bound_all ε h0 h1
  exact ⟨max x₀ 3, boxTail_CVal0_of h1 h⟩

theorem analyticEndClosed : AnalyticEndClosed := by
  obtain ⟨c', hc', h⟩ := analyticEndSel
  refine ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hZ hM => ?_⟩
  obtain ⟨C₂, hC₂, h1⟩ := boxCount_of_density hZ
  obtain ⟨x₂, h2⟩ := boxTail_CVal0 ε hε hε1
  exact h ε A C₂ CVal0 x₂ C₄ x₄ hε hε1 hA hC₂ hC₄ h1 h2 hM

theorem analyticEndClosedTied : AnalyticEndClosedTied := by
  obtain ⟨c', hc', h⟩ := analyticEndTied
  refine ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hZ hM => ?_⟩
  obtain ⟨C₂, hC₂, h1⟩ := boxCount_of_density hZ
  obtain ⟨x₂, h2⟩ := boxTail_CVal0 ε hε hε1
  exact h ε A C₂ CVal0 x₂ C₄ x₄ hε hε1 hA hC₂ hC₄ h1 h2 hM

theorem core_of_coreAt (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A Cord eD eL K cHH eK CL eW KW ε x : ℝ)
    (hP : LBr2.PrimePairBounds ε CL x q d) (h : CoreAt q d A Cord eD eL K cHH eK eW KW ε x) :
    LChain6.Chain6Core A Cord eD eL K cHH eK CL eW KW ε x := by
  obtain ⟨e, Ω, i1, W, i2, i3, m, k, C, N, TT, T2, a, btH, w, Fc, Rw, O, Lp, P, π, s, sB, BAD, Sig, η, κ, off, g₁, g₂, logOm,
    C0, cZ, cL, cE5, c5, C0S, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨e, q, d, inferInstance, inferInstance, Ω, i1, W, i2, i3, m, k, C, N, TT, T2, a, btH, w, Fc, Rw, O, Lp, P, π, s, sB, BAD,
    Sig, η, κ, off, g₁, g₂, logOm, C0, cZ, cL, cE5, c5, C0S, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hP, h11, h12, h13, h14, h15⟩

theorem chain6AtClosed : Chain6AtClosed := by
  obtain ⟨Cord, hC, h⟩ := chain6At
  obtain ⟨c', _, hE⟩ := analyticEndClosed
  refine ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hZ hM => ?_⟩
  obtain ⟨xa, hxa⟩ := h eD eL A K cHH eK CVal0 eW KW ε hε hε4 hA
  obtain ⟨xb, hxb⟩ := hE ε A C₄ x₄ hε (by linarith) hA hC₄ hZ hM
  refine ⟨max xa xb, fun x hx => ?_⟩
  obtain ⟨_, iq, id, hEnd⟩ := hxb x (le_trans (le_max_right _ _) hx)
  exact ⟨iq, id, fun hc => hxa x (le_trans (le_max_left _ _) hx)
    (core_of_coreAt _ _ A Cord eD eL K cHH eK CVal0 eW KW ε x hEnd.1 hc)⟩

end Formalism.L2.GlobalTheoryTheory.MergeGL2
