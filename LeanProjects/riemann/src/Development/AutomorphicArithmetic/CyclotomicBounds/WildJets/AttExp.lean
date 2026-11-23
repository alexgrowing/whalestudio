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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Chain.StepVac in
private theorem mu_exp' {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
  rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  exact this

private theorem att_exp' {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ0 : T} (hL : L.Is μ0)
    {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv (GlobalTheory.SquareExps.eta_exp hL τ))
  · simpa using h0

theorem UpperTheory.WildA.expEx :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p → ∃ (a b : D.what₂.Tau → ℚ) (e₁ e₂ : D.what₂.Tau → ℤ),
      (∀ τ, HasInfExp D (G.chrS p) τ (a τ)) ∧ (∀ τ, HasInfExp D (G.chrT p) τ (b τ)) ∧
      (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP p * (G.pS p).rank / 2) ∧ ∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP p * (G.pT p).rank / 2) := by
  intro D T L sc G μ₀ hL p hp
  have half : ∀ (c : ℤ) (n : ℕ), ∃ e : ℤ, (e : ℚ) = ((c : ℚ) - if Odd n then 1 / 2 else 0) + (-1) * (n : ℚ) / 2 := by
    intro c n
    rcases Nat.even_or_odd n with h | h
    · obtain ⟨k, hk⟩ := id h
      refine ⟨c - k, ?_⟩
      rw [if_neg (Nat.not_odd_iff_even.2 h), hk]; push_cast; ring
    · obtain ⟨k, hk⟩ := id h
      refine ⟨c - k - 1, ?_⟩
      rw [if_pos h, hk]; push_cast; ring
  cases p with
  | mu t i j => exact hp.elim
  | core i => exact hp.elim
  | top t j =>
    have hj : j < D.R.m := hp
    have hr0 : Even (G.V (.top j)).rank := by rw [GlobalTheory.FunObj.rank_top G (j := j) (by omega)]; exact even_rankX D j
    have hr1 : Even (G.V (.top (j + 1))).rank := by
      rw [GlobalTheory.FunObj.rank_top G (j := j + 1) (by omega)]; exact even_rankX D (j + 1)
    have hS : G.chrS (.top t j) = L.mu t (j + 1) := by
      simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, if_false]
    have hT : G.chrT (.top t j) = L.mu t (j + 1) := by
      simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
    have hce : ∀ τ, (((num D sc.cGap τ).e (j + 1) : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩ := fun τ =>
      num_e D sc.cGap τ (l := j + 1) (by omega) hj
    obtain ⟨k0, hk0⟩ := hr0
    obtain ⟨k1, hk1⟩ := hr1
    refine ⟨fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ), fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ),
      fun τ => -(num D sc.cGap τ).e (j + 1) + k0, fun τ => (num D sc.cGap τ).e (j + 1) - k1,
      fun τ => ?_, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
    · rw [hS]; exact mu_exp' hL t j hj τ
    · rw [hT]; exact mu_exp' hL t j hj τ
    · simp only [GlobalTheory.FockReal.sgnP, one_mul, hk0, ← hce]; push_cast; ring
    · simp only [GlobalTheory.FockReal.sgnP, one_mul, hk1, ← hce]; push_cast; ring
  | chi i j =>
    have hi : i < D.R.m := hp.1
    choose e he using half
    refine ⟨_, _, fun τ => e (cen D sc.cGap τ (D.R.m - i)) (G.pS (.chi i j : Pair T)).rank,
      fun τ => -e (cen D sc.cGap τ (D.R.m - i)) (G.pT (.chi i j : Pair T)).rank,
      fun τ => att_exp' G hL hi _ τ, fun τ => att_exp' G hL hi _ τ, fun τ => ?_, fun τ => ?_⟩
    · exact he _ _
    · rw [Int.cast_neg, he]; rfl
