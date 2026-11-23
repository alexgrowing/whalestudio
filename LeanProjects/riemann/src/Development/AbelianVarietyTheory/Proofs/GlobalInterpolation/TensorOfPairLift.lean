import Mathlib
import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
import Formalism.SharpRestriction.GrowthBounds.InitialMinorTransposeMemHighestWeight
import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
import Formalism.LocalToGlobal.GroupLattices.FockModels.LoBlockActComp
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains
import Formalism.SharpRestriction.GrowthBounds.FockGramWindow
import Formalism.SharpRestriction.GrowthBounds.WittIdentPI
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PolyUpperBoundDelta
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestAssumptionsOfThreeInterfaces
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCGlue
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCoreOfNum
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColTop
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColumnPolynomialCovectorZero
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KapCore
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankOnDigitsCast
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.StWeyl
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.AiAddMulLeA0
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockFG
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdStandardLarge
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NotKept
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfSLine
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeOfStd
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseThresholdRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WittPNe
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualFlatOf
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualLat
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PosCoreLetter
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCZ
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SegFormZeroRight
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TestFlat
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Beyond44OfRestRawTail
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PairedLiftAtOfIdentity
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.GTheta
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OPlusAtOf
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyMinorDvd
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PsiRes0Ne
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFFinal

noncomputable section

namespace GlobalTheory.EX.RangeOne

section Numbers

open Formalism.MainNotions.G Formalism.MainNotions.ColumnSystems Formalism.MainNotions.ColumnSystems.Pf

theorem core_roomR {b' g A P Q k c de be eps N Y N1 ka : ℝ} (hb : 0 < b') (hAP : g - k * P < A * P)
    (hbT : b' * (1 - be) ≤ g) (hbe : be ≤ de / 2 - 18 * eps) (heps : 0 ≤ eps) (hde6 : de < 1 / 6)
    (hde40 : 40 * eps ≤ de) (hepsk : 1 / k ≤ eps) (hk5 : 5 ≤ k) (hQ1 : 1 ≤ Q) (hP0 : 0 < P) (hPQ : P ≤ Q)
    (sq_level_le_degree : 2 * N1 + 3 ≤ k) (hN2 : 2 ≤ N) (hY1 : 1 ≤ Y) (hHc : 1 * k ^ 3 * N * Q ^ 4 * c * Y ≤ b')
    (hc1 : 1 ≤ c) (hA0 : 0 ≤ A) (hN10 : 0 ≤ N1) (hka : ka = 13 * k * N1 * Q) :
    c * (ka + 2 * Q + 3 * k) + 4 ≤ de / 4 * A := by
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 < Q := by linarith
  have hbe12 : be ≤ 1 / 12 := by linarith
  have h1 : b' * (11 / 12) ≤ b' * (1 - be) := mul_le_mul_of_nonneg_left (by linarith) hb.le
  have h2 : A * P ≤ A * Q := mul_le_mul_of_nonneg_left hPQ hA0
  have h3 : k * P ≤ k * Q := mul_le_mul_of_nonneg_left hPQ hk0.le
  have hAQ : b' * (11 / 12) - k * Q ≤ A * Q := by linarith
  have hQ2 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hk3 : 0 ≤ k ^ 3 := by positivity
  have hb2 : 2 * k ^ 3 * Q ^ 2 * c ≤ b' := by
    have a0 : 0 ≤ k ^ 3 * c := by positivity
    have a1 : 2 * k ^ 3 * Q ^ 2 * c ≤ 2 * k ^ 3 * Q ^ 4 * c := by
      have := mul_le_mul_of_nonneg_left hQ2 a0
      linarith
    have a5 : 0 ≤ k ^ 3 * Q ^ 4 * c := by positivity
    have a2 : 2 * (k ^ 3 * Q ^ 4 * c) ≤ N * (k ^ 3 * Q ^ 4 * c) := mul_le_mul_of_nonneg_right hN2 a5
    have a6 : 0 ≤ N * (k ^ 3 * Q ^ 4 * c) := by positivity
    have a3 : N * (k ^ 3 * Q ^ 4 * c) * 1 ≤ N * (k ^ 3 * Q ^ 4 * c) * Y := mul_le_mul_of_nonneg_left hY1 a6
    have a4 : 1 * k ^ 3 * N * Q ^ 4 * c * Y = N * (k ^ 3 * Q ^ 4 * c) * Y := by ring
    linarith
  have hA1 : ((11 / 6) * k ^ 3 * Q * c - k) * Q ≤ A * Q := by
    have e : ((11 / 6) * k ^ 3 * Q * c - k) * Q = (11 / 12) * (2 * k ^ 3 * Q ^ 2 * c) - k * Q := by ring
    rw [e]
    linarith
  have hA2 : (11 / 6) * k ^ 3 * Q * c - k ≤ A := le_of_mul_le_mul_right hA1 hQ0
  have hdek : 40 ≤ de * k := by
    have a1 : 40 * (1 / k) ≤ de := by linarith
    have a2 : 40 * (1 / k) * k = 40 := by field_simp
    have a3 : 40 * (1 / k) * k ≤ de * k := mul_le_mul_of_nonneg_right a1 hk0.le
    linarith
  have hfin : ((55 / 3) * k ^ 2 * Q * c - 10) * k ≤ de / 4 * A * k := by
    have a1 : 40 * A ≤ de * k * A := mul_le_mul_of_nonneg_right hdek hA0
    have a2 : ((55 / 3) * k ^ 2 * Q * c - 10) * k = (10 / 1) * ((11 / 6) * k ^ 3 * Q * c - k) := by ring
    have a3 : de / 4 * A * k = (de * k * A) / 4 := by ring
    rw [a2, a3]
    linarith
  have hfin2 : (55 / 3) * k ^ 2 * Q * c - 10 ≤ de / 4 * A := le_of_mul_le_mul_right hfin hk0
  have hN1 : N1 ≤ k := by linarith
  have hkaB : ka ≤ 13 * k ^ 2 * Q := by
    rw [hka]
    have a1 : k * N1 ≤ k * k := mul_le_mul_of_nonneg_left hN1 hk0.le
    have a2 : k * N1 * Q ≤ k * k * Q := mul_le_mul_of_nonneg_right a1 hQ0.le
    have e1 : 13 * k * N1 * Q = 13 * (k * N1 * Q) := by ring
    have e2 : 13 * k ^ 2 * Q = 13 * (k * k * Q) := by ring
    rw [e1, e2]
    linarith
  have hkQ : k ≤ k * Q := le_mul_of_one_le_right hk0.le hQ1
  have hk25 : 5 * 5 ≤ k * k := mul_le_mul hk5 hk5 (by norm_num) hk0.le
  have hk5k : 5 * k ≤ k * k := mul_le_mul_of_nonneg_right hk5 hk0.le
  have hc0 : 0 ≤ c := by linarith
  have hQc0 : 0 ≤ Q * c := mul_nonneg hQ0.le hc0
  have hQc1 : 1 ≤ Q * c := one_le_mul_of_one_le_of_one_le hQ1 hc1
  have hQc : 25 * (Q * c) ≤ k * k * (Q * c) := by
    have := mul_le_mul_of_nonneg_right hk25 hQc0
    linarith
  have hkQc : 5 * k * (Q * c) ≤ k * k * (Q * c) := mul_le_mul_of_nonneg_right hk5k hQc0
  have hX : k ^ 2 * Q * c = k * k * (Q * c) := by ring
  have hfirst : c * (ka + 2 * Q + 3 * k) ≤ c * (13 * k ^ 2 * Q + 2 * Q + 3 * (k * Q)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    linarith
  have e1 : c * (13 * k ^ 2 * Q + 2 * Q + 3 * (k * Q)) =
      13 * (k * k * (Q * c)) + 2 * (Q * c) + 3 * (k * (Q * c)) := by ring
  have e2 : 55 / 3 * k ^ 2 * Q * c = 55 / 3 * (k * k * (Q * c)) := by ring
  have e3 : 5 * k * (Q * c) = 5 * (k * (Q * c)) := by ring
  rw [e1] at hfirst
  rw [e2] at hfin2
  rw [e3] at hkQc
  linarith

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc}

theorem core_room (St : Std C0 Cde CE1 CE2 1 X) (hc : 1 ≤ X.c) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (hdig : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (i : Fin (segS X.TT j)) :
    (X.c : ℝ) * (ka1 X + 2 * X.Q + 3 * X.k) + 4 ≤
      X.de C0 Cde / 4 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
  have H := segHyp_of St j
  obtain ⟨hP0, -, -, hQ, hPQ⟩ := St.levels j i
  have hcb := coarse_bounds (X.bT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.rz i)
    (fun c => (hdig.1 i c).1) (hdig.2.1 i).1 (hdig.2.1 i).2
  have hAP : (X.bT (segPos X.TT j i) : ℝ) - X.k * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) <
      (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) := hcb.2
  have hbT : X.b' * (1 - _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ) := (H.bT i).1
  have hc1 : (1 : ℝ) ≤ (X.c : ℝ) := by exact_mod_cast hc
  exact core_roomR St.bpos hAP hbT St.be18 St.eps0 St.de6 St.forty_epsilon_le_delta St.eps_ge St.k5 St.Q1 hP0 (hPQ.trans hQ) St.N1k
    St.N2 St.Y1 St.Hc hc1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) rfl

theorem core_floor {x y : ℝ} {z : ℤ} (h : x + z ≤ y) : ⌊x⌋ + z ≤ ⌊y⌋ := by
  apply Int.le_floor.2
  push_cast
  linarith [Int.floor_le x]

theorem core_capdiff (p : ℕ) {s r : ℕ} (S : SegData s) (b b' : SegBlock s r) (l : ℕ) (D : ℤ) (hD : 0 ≤ D)
    (h : ∀ i : Fin s, ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) - ((coarseA p S b' i : ℤ) - (oEff S b' i : ℤ)) ≤ D) :
    cap p S b l - cap p S b' l ≤ (s : ℤ) * D := by
  unfold cap
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      (if (i : ℕ) < l then ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) else 0) -
        (if (i : ℕ) < l then ((coarseA p S b' i : ℤ) - (oEff S b' i : ℤ)) else 0) ≤ D := by
    intro i _
    split_ifs
    · exact h i
    · simpa using hD
  have h3 := Finset.sum_le_sum h2
  rw [Finset.sum_sub_distrib] at h3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  linarith

theorem core_termU {A A' o o' K q : ℕ} (hA : A ≤ A' + K) (ho : o' ≤ o + 2 * (K + q)) :
    ((A : ℤ) - (o : ℤ)) - ((A' : ℤ) - (o' : ℤ)) ≤ ((3 * K + 2 * q : ℕ) : ℤ) := by
  push_cast
  omega

theorem core_termS {A A' w w' g g' K q : ℕ} (hA : A ≤ A' + K) (hw : w' ≤ w + (K + q)) (hg : g' ≤ g + (K + q)) :
    ((A : ℤ) - ((w + g : ℕ) : ℤ)) - ((A' : ℤ) - ((w' + g' : ℕ) : ℤ)) ≤ ((3 * K + 2 * q : ℕ) : ℤ) := by
  push_cast
  omega

set_option maxHeartbeats 1600000 in

theorem numCore_std {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    NumCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X hD hH hcB mm _ n hn1 hnc e he1 hen j b hb
  have St := hstd X hD hH hcB
  have hc : 1 ≤ X.c := le_trans hn1 hnc
  obtain ⟨hdig, hU, hS, _, hP2⟩ := hb
  have hk5 := St.k5
  have hQ1 := St.Q1
  have hN1pos : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hde0 : 0 ≤ X.de C0 Cde := le_trans (mul_nonneg (by norm_num) St.eps0) St.forty_epsilon_le_delta
  have hde6 := St.de6
  have he1r : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hecr : (e : ℝ) ≤ X.c := by exact_mod_cast (le_of_lt (lt_of_lt_of_le hen hnc))
  have hkdef : X.k = (X.m : ℝ) + 1 := rfl
  have hQdef : X.Q = (X.p : ℝ) ^ X.G' := rfl
  have hk0 : 0 < X.k := by linarith
  have hQ0 : 0 < X.Q := by linarith
  have hka : ka1 X = 13 * X.k * X.N1 * X.Q := rfl
  have hkapos : 0 ≤ ka1 X := by
    rw [hka]
    have : (0 : ℝ) ≤ X.N1 := by linarith
    positivity
  have hE : (((X.c - n : ℕ)) : ℝ) ≤ X.c := by exact_mod_cast Nat.sub_le _ _
  have hE' : (((X.c - (n - e) : ℕ)) : ℝ) * ka1 X = ((X.c - n : ℕ) : ℝ) * ka1 X + e * ka1 X := by
    have : X.c - (n - e) = (X.c - n) + e := by omega
    rw [this]
    push_cast
    ring
  have hne : (((n - e : ℕ)) : ℝ) = (n : ℝ) - e := Nat.cast_sub (le_of_lt hen)

  have hkQ1 : 1 ≤ X.k * X.Q := one_le_mul_of_one_le_of_one_le (by linarith) hQ1
  have hQe1 : 1 ≤ X.Q * e := one_le_mul_of_one_le_of_one_le hQ1 he1r
  have hx : e * ka1 X = 13 * (X.N1 * X.k * X.Q * e) := by rw [hka]; ring
  have hN0 : (0 : ℝ) ≤ X.N1 := by linarith
  have b1 : (X.N1 : ℝ) * e ≤ X.N1 * X.k * X.Q * e := by
    have := mul_le_mul_of_nonneg_left hkQ1 (mul_nonneg hN0 (by linarith : (0:ℝ) ≤ e))
    nlinarith
  have b2 : (X.N1 : ℝ) * X.k ≤ X.N1 * X.k * X.Q * e := by
    have := mul_le_mul_of_nonneg_left hQe1 (mul_nonneg hN0 hk0.le)
    nlinarith
  have b3 : (X.N1 : ℝ) * (X.Q * e) ≤ X.N1 * X.k * X.Q * e := by
    have h1k : (1 : ℝ) ≤ X.k := by linarith
    have := mul_le_mul_of_nonneg_left h1k (mul_nonneg hN0 (by linarith : (0:ℝ) ≤ X.Q * e))
    nlinarith
  have b4 : X.k ≤ (X.N1 : ℝ) * X.k := le_mul_of_one_le_left hk0.le hN1pos
  have b5 : X.Q * e ≤ (X.N1 : ℝ) * (X.Q * e) := le_mul_of_one_le_left (by linarith) hN1pos
  have hnumA : 3 * X.k + 2 * (X.Q * e) ≤ e * ka1 X := by rw [hx]; linarith
  have hnumB : (X.N1 : ℝ) * e + ((X.N1 : ℝ) + 1) * (X.k + X.Q * e) + (X.N1 : ℝ) * (3 * X.k + 2 * (X.Q * e)) ≤
      e * ka1 X := by
    have e1 : (X.N1 : ℝ) * e + ((X.N1 : ℝ) + 1) * (X.k + X.Q * e) + (X.N1 : ℝ) * (3 * X.k + 2 * (X.Q * e)) =
        (X.N1 : ℝ) * e + 4 * ((X.N1 : ℝ) * X.k) + 3 * ((X.N1 : ℝ) * (X.Q * e)) + X.k + X.Q * e := by ring
    rw [e1, hx]
    linarith
  refine ⟨?_, ?_⟩
  ·
    intro i hi
    obtain ⟨-, hoR, -, -⟩ := hU i hi
    have room := core_room St hc j b hdig i
    have hEk : (((X.c - n : ℕ)) : ℝ) * ka1 X ≤ X.c * ka1 X := mul_le_mul_of_nonneg_right hE hkapos
    have hQec : X.Q * e ≤ X.Q * X.c := mul_le_mul_of_nonneg_left hecr hQ0.le
    have hkc : 0 ≤ X.k * X.c := by positivity
    have goalR : ((1 + 2 * (X.p ^ X.G' * e) + b.o i : ℕ) : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
      push_cast
      rw [← hQdef]
      have e1 : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde / 4) =
          (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) - X.de C0 Cde / 4 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
        ring
      have e2 : (X.c : ℝ) * (ka1 X + 2 * X.Q + 3 * X.k) = X.c * ka1 X + 2 * (X.Q * X.c) + 3 * (X.k * X.c) := by ring
      rw [e1] at hoR
      rw [e2] at room
      linarith
    exact_mod_cast goalR
  · intro b' hdig' hA hU' hS' hP1' hP2'
    refine ⟨⟨hdig', ?_, ?_, hP1', ?_⟩, ?_⟩
    · intro i hi
      obtain ⟨h1, h2, h3, h4⟩ := hU' i hi
      obtain ⟨-, hoR, -, -⟩ := hU i hi
      refine ⟨h1, ?_, h3, h4⟩
      have h2R : (b'.o i : ℝ) ≤ (b.o i : ℝ) + 2 * (X.k + X.Q * e) := by
        have := (Nat.cast_le (α := ℝ)).2 h2
        push_cast at this
        rw [hkdef, hQdef]
        linarith
      have hAR : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) + X.k := by
        have := (Nat.cast_le (α := ℝ)).2 (hA i)
        push_cast at this
        rw [hkdef]
        linarith
      have hm : 0 ≤ 1 - X.de C0 Cde / 4 := by linarith
      have h5 := mul_le_mul_of_nonneg_right hAR hm
      have h6 : X.k * (1 - X.de C0 Cde / 4) ≤ X.k := by nlinarith
      rw [hE']
      have e1 : ((coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) + X.k) * (1 - X.de C0 Cde / 4) =
          (coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) * (1 - X.de C0 Cde / 4) + X.k * (1 - X.de C0 Cde / 4) := by ring
      rw [e1] at h5
      linarith
    · intro i hi
      obtain ⟨h1, h2, h3, h4, -⟩ := hS' i hi
      obtain ⟨-, -, -, hsR⟩ := hS i hi
      refine ⟨h1, h2, h3, ?_⟩
      have h4R : (b'.sg i : ℝ) ≤ (b.sg i : ℝ) + (X.k + X.Q * e) := by
        have := (Nat.cast_le (α := ℝ)).2 h4
        push_cast at this
        rw [hkdef, hQdef]
        linarith
      rw [hE']
      linarith
    · have hPR : (b'.oPlus : ℝ) ≤ (b.oPlus : ℝ) + X.Q * e := by
        have := (Nat.cast_le (α := ℝ)).2 hP2'
        push_cast at this
        rw [hQdef]
        linarith
      rw [hE']
      linarith
    · intro l V hV
      have hterm : ∀ i : Fin (segS X.TT j),
          ((coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℤ) - (oEff (X.seg C0 CE1 CE2 j) b i : ℤ)) -
            ((coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℤ) - (oEff (X.seg C0 CE1 CE2 j) b' i : ℤ)) ≤
            ((3 * (X.m + 1) + 2 * (X.p ^ X.G' * e) : ℕ) : ℤ) := by
        intro i
        by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
        · have e1 : oEff (X.seg C0 CE1 CE2 j) b i = b.w i + b.sg i := if_pos hi
          have e2 : oEff (X.seg C0 CE1 CE2 j) b' i = b'.w i + b'.sg i := if_pos hi
          rw [e1, e2]
          obtain ⟨-, -, -, hg, hw⟩ := hS' i hi
          exact core_termS (hA i) hw hg
        · have e1 : oEff (X.seg C0 CE1 CE2 j) b i = b.o i := if_neg hi
          have e2 : oEff (X.seg C0 CE1 CE2 j) b' i = b'.o i := if_neg hi
          rw [e1, e2]
          obtain ⟨-, ho, -, -⟩ := hU' i (not_lt.1 hi)
          exact core_termU (hA i) ho
      have hcd := core_capdiff X.p (X.seg C0 CE1 CE2 j) b b' l _ (by positivity) hterm
      have hcdR := (Int.cast_le (R := ℝ)).2 hcd
      push_cast at hcdR
      have hsN : ((segS X.TT j : ℕ) : ℝ) ≤ X.N1 := by exact_mod_cast (St.segB j).2
      have hD0 : (0 : ℝ) ≤ 3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e) := by positivity
      have hsD := mul_le_mul_of_nonneg_right hsN hD0
      have hVR := (Int.cast_le (R := ℝ)).2 hV
      push_cast at hVR
      rw [add_assoc]
      apply core_floor
      rw [hne]
      push_cast
      rw [hkdef, hQdef] at hnumB
      have e1 : (mm + (n : ℝ) * ka1 X) - (mm + ((n : ℝ) - e) * ka1 X) = e * ka1 X := by ring
      have e2 : (X.N1 : ℝ) * (3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e)) =
          (X.N1 : ℝ) * (3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e)) := rfl
      linarith

theorem numCore_thr : RestNumCore :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => numCore_std h.2) thr_std

set_option maxHeartbeats 3200000 in

theorem keptPair_bounds {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    PairSAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hP hK i hi
  have hs := hstd X hD hI hc
  have hk5 := hs.k5
  have hk : (0 : ℝ) < X.k := by linarith
  have hkk : X.k = (X.m : ℝ) + 1 := rfl
  have hLK := hs.LaK
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast hs.N1pos
  have hLa1 := hs.La1
  have hLa0 : (0 : ℝ) ≤ X.La C0 := le_trans zero_le_one hLa1
  have hde6 := hs.de6
  have hp0 : (0 : ℝ) < X.p := by have := hs.p5; exact_mod_cast (show 0 < X.p by omega)
  have hp2pos : (0 : ℝ) < (X.p : ℝ) ^ 2 := by positivity
  have hp25 : (25 : ℝ) ≤ (X.p : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ X.p := by exact_mod_cast hs.p5
    nlinarith
  have hde0 : 0 ≤ X.de C0 Cde := le_trans (by positivity) hLK
  set A0 : ℝ := ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) with hA0
  set Aa : Fin (segS X.TT j) → ℝ := fun l => (clA C0 CE1 CE2 X j rz ry l : ℝ) with hAa

  have hAl : ∀ l : Fin (segS X.TT j), l.val ≤ i.val → Aa l ≤ A0 := by
    intro l hl
    have h := (coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd l).1 (lt_of_le_of_lt hl hi)
    have h0 : (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry l : ℝ) := Nat.cast_nonneg _
    show (clA C0 CE1 CE2 X j rz ry l : ℝ) ≤ _
    nlinarith
  have hAnn : ∀ l : Fin (segS X.TT j), (0 : ℝ) ≤ Aa l := fun l => by
    show (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry l : ℝ); exact Nat.cast_nonneg _
  have hA00 : (0 : ℝ) ≤ A0 := le_trans (hAnn i) (hAl i le_rfl)
  have h4p : 4 / (X.p : ℝ) ^ 2 ≤ 1 := by rw [div_le_one hp2pos]; linarith

  have hsum : ∀ l : Fin (segS X.TT j), (∑ x : Fin (segS X.TT j), if x.val < l.val then Aa x else 0) ≤ 4 * Aa l / (X.p : ℝ) ^ 2 :=
    fun l => coarse_degree_prefix_sum hs le_rfl j rz ry hd l

  have hkap : ∀ l : Fin (segS X.TT j), ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤ 4 * Aa l / (X.p : ℝ) ^ 2 := by
    intro l
    have h1 := pf_prev_le hP.1 l.val (by omega)
    have h2 : ((∑ x : Fin (segS X.TT j), if x.val < l.val then pairW mu x.val else 0 : ℤ) : ℝ) ≤
        ∑ x : Fin (segS X.TT j), if x.val < l.val then Aa x else 0 := by
      push_cast
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs
      · obtain ⟨-, -, -, hw, -, -, -, -⟩ := pair_top hP.1 x
        show _ ≤ ((clA C0 CE1 CE2 X j rz ry x : ℕ) : ℝ)
        exact_mod_cast hw
      · exact le_rfl
    have h1' : ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤
        ((∑ x : Fin (segS X.TT j), if x.val < l.val then pairW mu x.val else 0 : ℤ) : ℝ) := by exact_mod_cast h1
    linarith [hsum l]
  have hrho : ∀ l : Fin (segS X.TT j), ((pairRho mu l.val : ℤ) : ℝ) ≤ Aa l + 4 * Aa l / (X.p : ℝ) ^ 2 := by
    intro l
    have h1 := pf_rho_le hP.1 l
    obtain ⟨-, -, -, hw, -, -, -, -⟩ := pair_top hP.1 l
    have h1' : ((pairRho mu l.val : ℤ) : ℝ) ≤ ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) +
        ((pairW mu l.val : ℤ) : ℝ) := by exact_mod_cast h1
    have hw' : ((pairW mu l.val : ℤ) : ℝ) ≤ Aa l := by
      show _ ≤ ((clA C0 CE1 CE2 X j rz ry l : ℕ) : ℝ)
      exact_mod_cast hw
    linarith [hkap l]

  have hcup : ∀ l : Fin (segS X.TT j), l.val ≤ i.val → ((pairC mu l.val : ℤ) : ℝ) ≤ 2 * A0 := by
    intro l hl
    have h1 := pairC_le_sum hP.1 l
    have hA : (A : ℝ) ≤ A0 := hA2
    have h3 : 4 * Aa l / (X.p : ℝ) ^ 2 ≤ Aa l := by
      have e : 4 * Aa l / (X.p : ℝ) ^ 2 = Aa l * (4 / (X.p : ℝ) ^ 2) := by ring
      rw [e]; nlinarith [hAnn l]
    have := hsum l
    have := hAl l hl
    simp only [hAa] at *
    linarith

  have hkept : ∀ l : Fin (segS X.TT j), ((pairO mu (clA C0 CE1 CE2 X j rz ry) l : ℤ) : ℝ) - ((pairRho mu l.val : ℤ) : ℝ) +
      4 * (Aa l + X.m) / (X.p : ℝ) ^ 2 ≤ X.La C0 * max ((pairC mu l.val : ℤ) : ℝ) (Aa l) / X.k := by
    intro l
    have h := (hK l).1
    rw [hkk]
    push_cast at h ⊢
    exact h

  set δ : ℝ := 3 * A0 * (4 / (X.p : ℝ) ^ 2 + X.La C0 / X.k) with hδ
  have hlow : ∀ n : ℕ, ∀ hn : n ≤ i.val, (A : ℝ) - n * δ ≤ ((pairC mu n : ℤ) : ℝ) := by
    intro n
    induction n with
    | zero => intro _; rw [pairC_zero hP.1]; simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      set l : Fin (segS X.TT j) := ⟨n, by omega⟩ with hl
      have eC : pairC mu (n + 1) = pairC mu n + ((clA C0 CE1 CE2 X j rz ry l : ℕ) : ℤ) -
          pairO mu (clA C0 CE1 CE2 X j rz ry) l := by unfold pairO; ring
      have hk1 := hkept l
      have hr := hrho l
      have hcl := hcup l (by show n ≤ i.val; omega)
      have hal := hAl l (by show n ≤ i.val; omega)
      have hmax : max ((pairC mu n : ℤ) : ℝ) (Aa l) ≤ 2 * A0 := max_le hcl (by linarith)
      have hLk : 0 ≤ X.La C0 / X.k := div_nonneg hLa0 hk.le
      have hm0 : (0 : ℝ) ≤ 4 * (Aa l + X.m) / (X.p : ℝ) ^ 2 := by
        have := hAnn l; positivity
      have hOl : ((pairO mu (clA C0 CE1 CE2 X j rz ry) l : ℤ) : ℝ) ≤ Aa l + 4 * Aa l / (X.p : ℝ) ^ 2 +
          X.La C0 * (2 * A0) / X.k := by
        have : X.La C0 * max ((pairC mu n : ℤ) : ℝ) (Aa l) / X.k ≤ X.La C0 * (2 * A0) / X.k := by
          apply div_le_div_of_nonneg_right _ hk.le
          exact mul_le_mul_of_nonneg_left hmax hLa0
        simp only [hl] at hk1 hr ⊢
        linarith
      have hd1 : 4 * Aa l / (X.p : ℝ) ^ 2 + X.La C0 * (2 * A0) / X.k ≤ δ := by
        have e1 : 4 * Aa l / (X.p : ℝ) ^ 2 ≤ 3 * A0 * (4 / (X.p : ℝ) ^ 2) := by
          have e : 4 * Aa l / (X.p : ℝ) ^ 2 = Aa l * (4 / (X.p : ℝ) ^ 2) := by ring
          rw [e]
          have : (0 : ℝ) ≤ 4 / (X.p : ℝ) ^ 2 := by positivity
          nlinarith
        have e2 : X.La C0 * (2 * A0) / X.k ≤ 3 * A0 * (X.La C0 / X.k) := by
          have e : X.La C0 * (2 * A0) / X.k = 2 * A0 * (X.La C0 / X.k) := by ring
          rw [e]; nlinarith
        rw [hδ]; linarith
      rw [eC]
      push_cast
      simp only [hl] at hOl hd1
      linarith

  have hci_low := hlow i.val le_rfl
  have hsN : (i.val : ℝ) ≤ X.N1 := by
    have := (hs.segB j).2
    have : i.val ≤ X.N1 := by omega
    exact_mod_cast this
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hAlo : A0 * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) := hA1
  have hdich := (coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd i).1 hi

  have sq_level_le_degree : 2 * (X.N1 : ℝ) + 3 ≤ X.k := hs.N1k
  have hkp : X.k ^ 2 ≤ (X.p : ℝ) := by
    have hY2 : (1 : ℝ) ≤ X.Y ^ 2 := one_le_pow₀ hs.Y1
    nlinarith [hs.pk, mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)]
  have hde40 : 40 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde := hLK
  have hq1 : 4 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde / 10 := by
    have e : 4 * X.N1 * X.La C0 / X.k = (40 * X.N1 * X.La C0 / X.k) / 10 := by ring
    rw [e]; linarith
  have hq2 : 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde / 80 := by
    have hk4 : X.k ^ 4 ≤ (X.p : ℝ) ^ 2 := by
      calc X.k ^ 4 = (X.k ^ 2) ^ 2 := by ring
        _ ≤ (X.p : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hkp 2
    have h40 : 40 / X.k ≤ X.de C0 Cde := by
      refine le_trans ?_ hde40
      rw [div_le_div_iff_of_pos_right hk]
      have h1 : 1 ≤ (X.N1 : ℝ) * X.La C0 := one_le_mul_of_one_le_of_one_le hN1 hLa1
      have e : 40 * (X.N1 : ℝ) * X.La C0 = 40 * ((X.N1 : ℝ) * X.La C0) := by ring
      rw [e]; linarith
    have hN1le : (X.N1 : ℝ) ≤ X.k := by linarith
    have h1 : 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ 12 * X.k / X.k ^ 4 := by
      apply div_le_div₀ (by positivity) (by linarith) (by positivity) hk4
    have h2 : 12 * X.k / X.k ^ 4 ≤ (40 / X.k) / 80 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hk3 : (5 : ℝ) ^ 3 ≤ X.k ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hk5 3
        exact this
      nlinarith [mul_le_mul_of_nonneg_left hk3 (by positivity : (0:ℝ) ≤ X.k ^ 2)]
    have h3 : (40 / X.k) / 80 ≤ X.de C0 Cde / 80 := by linarith
    linarith
  have hci_ge : Aa i ≤ ((pairC mu i.val : ℤ) : ℝ) := by

    have h1 : (i.val : ℝ) * δ ≤ X.N1 * δ := mul_le_mul_of_nonneg_right hsN hδ0
    have hexp : X.N1 * δ = A0 * (12 * X.N1 / (X.p : ℝ) ^ 2 + 3 * X.N1 * X.La C0 / X.k) := by
      rw [hδ]; ring
    have hlow2 : A0 * (1 - (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2)) ≤ ((pairC mu i.val : ℤ) : ℝ) := by
      have e : A0 * (1 - X.N1 * X.La C0 / X.k) = A0 - A0 * (X.N1 * X.La C0 / X.k) := by ring
      have e2 : A0 * (1 - (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2)) =
          A0 - A0 * (X.N1 * X.La C0 / X.k) - A0 * (12 * X.N1 / (X.p : ℝ) ^ 2 + 3 * X.N1 * X.La C0 / X.k) := by ring
      rw [e2]
      linarith
    have hε : (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2) * (1 + X.de C0 Cde) ≤ X.de C0 Cde := by
      have hsum' : 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde * (9 / 80) := by linarith
      have hε0 : 0 ≤ 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 := by positivity
      nlinarith

    have key : Aa i * (1 + X.de C0 Cde) ≤ A0 := le_of_lt hdich
    set ε : ℝ := 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 with hεd
    have hε1 : 0 ≤ 1 - ε := by linarith
    have hprod : 1 ≤ (1 + X.de C0 Cde) * (1 - ε) := by nlinarith
    have g1 : Aa i ≤ Aa i * ((1 + X.de C0 Cde) * (1 - ε)) := le_mul_of_one_le_right (hAnn i) hprod
    have g2 : Aa i * ((1 + X.de C0 Cde) * (1 - ε)) ≤ A0 * (1 - ε) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right key hε1
    linarith
  have hmaxc : max ((pairC mu i.val : ℤ) : ℝ) (Aa i) = ((pairC mu i.val : ℤ) : ℝ) := max_eq_left hci_ge
  have hk1 := hkept i
  rw [hmaxc] at hk1
  have hm0 : (0 : ℝ) ≤ 4 * (Aa i + X.m) / (X.p : ℝ) ^ 2 := by have := hAnn i; positivity
  have hr := hrho i
  refine ⟨?_, ?_⟩
  · have e : Aa i * (1 + 4 / (X.p : ℝ) ^ 2) = Aa i + 4 * Aa i / (X.p : ℝ) ^ 2 := by ring
    show _ ≤ Aa i * (1 + 4 / (X.p : ℝ) ^ 2) + X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k
    rw [e]
    linarith
  ·
    have hu := pf_u_ge hP.1 i
    have hu' : ((pairSg mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) -
        ((mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤
        ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) - ((pairRho mu i.val : ℤ) : ℝ) := by exact_mod_cast hu
    have hkp' := hkap i
    have h4 : 4 * Aa i / (X.p : ℝ) ^ 2 ≤ 4 * (Aa i + X.m) / (X.p : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hp2pos.le
      have : (0 : ℝ) ≤ X.m := Nat.cast_nonneg _
      linarith
    have hc2 := hcup i le_rfl
    have hfin : X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k ≤ 2 * X.La C0 * A0 / X.k := by
      apply div_le_div_of_nonneg_right _ hk.le
      nlinarith
    linarith

theorem keptPair_thr : RestPairS :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      keptPair_bounds fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc

theorem keptBlocks : KeptBlocksBeyondThreshold := kept_blocks_of_S_line keptPair_thr

theorem closed_of_bounds {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (hU : RestUp) (hL : RestLow) (hL1 : PartnersToFactors)
    (hLift : RestLift) : Closed (ExtendedAllConclusions D) :=
  have hA2 : RemainderSegmentBoundSecond D := restAlt2_of (restSegLow_of hL) (dimHH_of h3) charZeroAt
  closed_of_rests (fun _ _ _ => segment_statement_holds D _ _ _) (restFree D) (remainderSegmentBoundFirst D) (rest2 D) (restAlt3 D)
    (one_segment_of_upper_lower hU hL) hA2 (restExt_of restRk hL1 hLift hA2)

theorem tensor_of_pairLift {D : Formalism.BasicNotions.D7} (h : admitted D → RestPairLift) : ExtendedClosedForm D := fun hA =>
  have hPL := h hA
  have hY : DimYAt := dimY_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 (stWeylAt D)
  have hCD : ChainDimAt := chainDim_of hY
  have hNB : NumBranchAt := numBranch_of hA.2.1 hA.2.2.1
  have hT : RestTail := restTail_of hCD hNB restPairCount
    (restNotKeptWt_of (wtBound_of hCD) (restBracket_of (restPairFacts_of restNUp) coarse_degrees_large_holds))
  have hB : BlockRankAt := blockRankAt
  have hCU : RestCountUp := upper_count_of_top_rows hCD hNB top_rows_bound_holds
  have hMU : RestMatchUp := restMatchUp_of (restFirstRows_of (restSTopRows_of top_rows_bound_holds))
  have hCL : RestCountLow := restCountLow_of'' hCD hT hMU keptBlocks
  closed_of_bounds hA.2.2.1 (restUp_of hB hY charZeroAt hCU) (restLow_of hB hY charZeroAt hCL) partners_to_factors_holds
    (restLift_of (restLiftVec_of hPL))

theorem tensor_closed (D : Formalism.BasicNotions.D7) : ExtendedClosedForm D :=
  tensor_of_pairLift fun hA =>
    paired_lifts_of_identity hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (restRawTail1_of (third_key_of_order key3Ord) (local_fourth_of_order (loc4Ord_of (loc4Div_of loc4Res)))
        (rest_assumptions_of_three_interfaces hA restCols restPre (restTCore_of_seg (restSegCore_of_num numCore_thr))))
      (restForm_of_oplus (Formalism.MainNotions.G.GLWeightTheory.lemma_five_two_first_holds D) restOPlus)

end Numbers

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G

theorem tools : ExtremalProjectorTools where
  extremalProjectorAlt := ExtremalProjector.extremal_projector_statement

theorem inputs : Loc8All where
  p13B := flipOneThree.Pf.theorem_I_closed_form_holds
  p13A := GramWindowAlt.theorem_A_closed_form_holds
  p15 := tensor_closed
  windowClauseTwo := Model.gl_branching_dimension
  windowClauseThree := Model.weyl_dual_weight_admissible
  lWeylV := Model.weylV_proved
  lWitt := WittPI.wittIdentity_holds
  tFlatTop := Model.flatTop
  tFlatHH := Model.flatHH
  hyperLatticeBasis := Model.dualHeightBasis
  hyperDualInclusion := Model.dualInclusionLattices
  tBePerfect := Model.bePerfect
  tHLSpans := Model.hlSpans
  tTestSide := Model.testSide
  tLPOneEvery := Model.lPOneEvery
  tCartanDomain := Model.cartanDomain_proved
  tCartanOnto := Model.cartanOnto_proved
  tKP1 := CountingStatementReduction.key_positivity_condition
  tKP2 := Joints.saturated_restriction_holds
  tKP3 := Joints.restriction_dimension_holds
  tRES := CountingStatementReduction.residue_division_transfer
  thresholdClauseOne := CountingStatementReduction.positivity_condition_eventually
  thresholdClauseThree := CountingStatementReduction.exponent_bound_eventually
  instanceClauseEight := fun D X => PolBridge.combined_weight_of_nested_sets D X (GLWeightTheory.weight_condition_from_integral_form D) (ColumnFamilies.Top.b15 D)

theorem rangeOne_abs :
    ∃ (T0 : ℝ) (T2 C : ℝ → ℝ), 0 < T0 ∧ ∀ C₀ : ℝ, T0 ≤ C₀ → 0 < T2 C₀ ∧ 0 < C C₀ ∧ ∀ CH : ℝ, T2 C₀ ≤ CH →
      ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.flipOneThree.Conclusion2 D C₀ CH (C C₀) :=
  first_theorem_threshold_functions tools inputs

end GlobalTheory.EX.RangeOne
