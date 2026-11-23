import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.WtBdWtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem bigN_le_sc_b {D : D7} {large₂ : SizeData₂ D} {Pm : ParameterChoice' D large₂} (P : ParamsT D large₂ Pm)
    (hf : 1 ≤ D.R.f) (hm : 1 ≤ D.R.m) : (bigN D : ℝ) ≤ large₂.sc.b := by
  have hx : 1 ≤ large₂.sc.x ^ P.Cb := Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) P.Cb_nonneg
  have hb := P.precision_cube_order_sq_le
  have hPPn := P.PP_nW
  have hNle := P.nW_le
  have h40 := P.TO_40
  have hsplit := P.split
  have hnP := P.nP_eq
  obtain ⟨hlo1, hlo2, hlo3⟩ := P.nW_lo
  have hN4 : 4 ≤ P.nWn := by omega
  have hk : D.R.k ≤ P.nWn + 1 := by
    have : D.R.k - 1 ≤ (D.R.k - 1) * D.R.f := Nat.le_mul_of_pos_right _ hf
    omega
  have hr : D.R.r ≤ P.nWn := by omega
  have ht : D.R.t ≤ P.nWn + P.TO * P.nWn := by omega
  have hmN : D.R.m ≤ (2 * D.R.f * D.R.m) ^ 4 * P.nWn := by
    calc D.R.m ≤ 2 * D.R.f * D.R.m := by nlinarith
      _ ≤ (2 * D.R.f * D.R.m) ^ 4 := Nat.le_self_pow (by norm_num) _
      _ ≤ (2 * D.R.f * D.R.m) ^ 4 * P.nWn := Nat.le_mul_of_pos_right _ (by omega)
  have hbig : bigN D ≤ (P.nWn + 1) + D.R.m * (P.TO * P.nWn + 2 * P.nWn + 7) := by
    unfold bigN sLen
    have : D.R.m * (D.R.t + (D.R.r + 6) + 1) ≤ D.R.m * (P.TO * P.nWn + 2 * P.nWn + 7) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    omega
  have hmR : (D.R.m : ℝ) ≤ P.PP := by
    have : ((D.R.m : ℕ) : ℝ) ≤ (((2 * D.R.f * D.R.m) ^ 4 * P.nWn : ℕ) : ℝ) := by exact_mod_cast hmN
    push_cast at this
    linarith
  have hNR : (P.nWn : ℝ) ≤ P.PP := hNle
  have hN4R : (4 : ℝ) ≤ P.nWn := by exact_mod_cast hN4
  have hTR : (40 : ℝ) ≤ P.TO := by
    have : 40 * (P.Dp + 2) ≤ P.TO := h40
    have : 40 ≤ P.TO := by omega
    exact_mod_cast this
  have hbigR : (bigN D : ℝ) ≤ (P.nWn + 1) + D.R.m * (P.TO * P.nWn + 2 * P.nWn + 7) := by
    exact_mod_cast hbig
  have hPP1 : 1 ≤ P.PP := by linarith
  have hm0 : (0 : ℝ) ≤ D.R.m := by positivity
  have hT0 : (0 : ℝ) ≤ P.TO := by positivity
  have hN0 : (0 : ℝ) ≤ P.nWn := by positivity
  have step1 : ((P.nWn : ℝ) + 1) + D.R.m * (P.TO * P.nWn + 2 * P.nWn + 7)
      ≤ P.PP ^ 2 * P.TO ^ 2 := by
    have e1 : (D.R.m : ℝ) * (P.TO * P.nWn + 2 * P.nWn + 7) ≤ P.PP * (P.TO * P.PP + 2 * P.PP + 7) := by
      apply mul_le_mul hmR _ (by positivity) (by linarith)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hPP1 (by linarith : (0:ℝ) ≤ P.PP)]
  have step2 : P.PP ^ 2 * P.TO ^ 2 ≤ P.PP ^ 3 * P.TO ^ 2 * large₂.sc.x ^ P.Cb := by
    have h3 : P.PP ^ 2 ≤ P.PP ^ 3 := by nlinarith [sq_nonneg P.PP]
    have hT2 : (0 : ℝ) ≤ P.TO ^ 2 := by positivity
    calc P.PP ^ 2 * P.TO ^ 2 ≤ P.PP ^ 3 * P.TO ^ 2 := mul_le_mul_of_nonneg_right h3 hT2
      _ = P.PP ^ 3 * P.TO ^ 2 * 1 := by ring
      _ ≤ P.PP ^ 3 * P.TO ^ 2 * large₂.sc.x ^ P.Cb := mul_le_mul_of_nonneg_left hx (by positivity)
  linarith

theorem UpperTheory.WildA.kerLe :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → sc.cGap = 1 → ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p →
      ((∑ τ, ∑ a, (wt G p.big τ).natW a : ℕ) : ℝ) + (D.R.f : ℝ) * (G.V p.small).rank * (G.V p.big).rank ≤ 13 * D.R.f * bigN D * large₂.sc.b := by
  intro D T L sc G large₂ hS hH hc p hp
  have hw : ∀ τ a, (((wt G p.big τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b :=
    fun τ a => wtBd large₂ hS hH hc p hp τ a
  obtain ⟨⟨Pm, P, -⟩, -, hmf, hm44, -⟩ := hS
  have hm : 1 ≤ D.R.m := by omega
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have hNb := bigN_le_sc_b P hf hm
  have hnodes : DefNode D.R.m p.big ∧ DefNode D.R.m p.small := by
    cases p with
    | chi i j =>
      obtain ⟨h1, h2⟩ := hp
      exact ⟨⟨h1, h2⟩, ⟨by omega, h2⟩⟩
    | mu t i j => exact hp.elim
    | core i => exact hp.elim
    | top t j =>
      exact ⟨show j + 1 ≤ D.R.m from hp, show j ≤ D.R.m by have : j + 1 ≤ D.R.m := hp; omega⟩
  have rb : ((G.V p.big).rank : ℝ) ≤ bigN D := by exact_mod_cast GlobalTheory.DefRank.rank_le_bigN G p.big hnodes.1
  have rs : ((G.V p.small).rank : ℝ) ≤ bigN D := by exact_mod_cast GlobalTheory.DefRank.rank_le_bigN G p.small hnodes.2
  have hsum : ((∑ τ, ∑ a, (wt G p.big τ).natW a : ℕ) : ℝ) ≤ D.R.f * (G.V p.big).rank * (12 * large₂.sc.b) := by
    push_cast
    calc (∑ τ, ∑ a, (((wt G p.big τ).natW a : ℕ) : ℝ))
        ≤ ∑ τ : D.what₂.Tau, ∑ a : Fin (G.V p.big).rank, 12 * large₂.sc.b :=
          Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun a _ => hw τ a
      _ = D.R.f * (G.V p.big).rank * (12 * large₂.sc.b) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, D.what₂.card_Tau]
          ring
  have hb0 : (0 : ℝ) ≤ large₂.sc.b := le_trans (by positivity) hNb
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have hrb0 : (0 : ℝ) ≤ (G.V p.big).rank := by positivity
  have hrs0 : (0 : ℝ) ≤ (G.V p.small).rank := by positivity
  have e1 : (D.R.f : ℝ) * (G.V p.big).rank * (12 * large₂.sc.b) ≤ 12 * D.R.f * bigN D * large₂.sc.b := by
    have := mul_le_mul_of_nonneg_left rb (by positivity : (0:ℝ) ≤ 12 * D.R.f * large₂.sc.b)
    nlinarith
  have e2 : (D.R.f : ℝ) * (G.V p.small).rank * (G.V p.big).rank ≤ D.R.f * bigN D * large₂.sc.b := by
    have hsb : ((G.V p.small).rank : ℝ) ≤ large₂.sc.b := le_trans rs hNb
    have h1 : ((G.V p.small).rank : ℝ) * (G.V p.big).rank ≤ large₂.sc.b * bigN D :=
      mul_le_mul hsb rb hrb0 hb0
    have := mul_le_mul_of_nonneg_left h1 hf0
    nlinarith
  linarith
