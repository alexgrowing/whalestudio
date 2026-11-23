import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetVacuumEqConstMulPeriodScaledJetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsOriginOppositeSignVacuumConjPeriodStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_delta (D : D7) : ∃ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ ∧ δ ≠ 0 := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK 1)) (n := 12) (by norm_num)
  refine ⟨δ, ⟨Formalism.MainNotions.GlobalTheoryTheory.jnt_ccK_curve D, hδ⟩, ?_⟩
  rintro rfl
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_one D D.host.ccK_ne_bot
  exact GlobalTheory.CurveLattice.discr_ne_zero _ L hL (by rw [← hδ]; simp)

theorem period_ne_zero {D : D7} {δ : ℂ} (hδ : δ ≠ 0) (τ : D.what₂.Tau) : period δ τ ≠ 0 := by
  refine div_ne_zero hδ (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ?_))
  have : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero)
  positivity

theorem rank_grid_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (k : ℕ) (hk : k ≤ D.R.m) :
    (G.V (.grid 0 k)).rank = D.R.r + k * D.R.t := by
  have key : (columnBlock L k).sp.rank = D.R.r + k * D.R.t := by
    rcases hk.eq_or_lt with rfl | hk
    · rw [colY_m]; exact D.sp.X'_rank
    · rw [colY_lt L hk]
      exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  exact key

theorem rank_node {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) {X : Node}
    (h : X.InRange D.R.m) (h0 : ∀ j, X ≠ .grid 0 j) : (G.V X).rank = X.rank D := (G.isV h h0).rank

theorem even_rank_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (p : Pair T),
    DefPair D.R.m p → Even ((G.pS p).rank * (G.pT p).rank) := by
  intro D T L sc G p hp
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have h1 : (G.pS (.chi i D.R.m)).rank = rankV D (i + 1) D.R.m :=
      rank_node G (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
    have h2 : (G.pT (.chi i D.R.m)).rank = rankV D i D.R.m := by
      rcases i with _ | i
      · show (G.V (.grid 0 D.R.m)).rank = _
        rw [rank_grid_zero G _ le_rfl]; simp [rankV]
      · exact rank_node G (X := .grid (i + 1) D.R.m) ⟨by omega, le_rfl⟩ (fun j h => by cases h)
    rw [h1, h2]
    have hs : Odd (sLen D) := odd_sLen D
    have e : rankV D (i + 1) D.R.m = rankV D i D.R.m + sLen D := by simp only [rankV]; ring
    by_cases he : Even (rankV D i D.R.m)
    · exact he.mul_left _
    · refine Even.mul_right ?_ _
      rw [e, Nat.even_add]
      exact ⟨fun h => absurd h he, fun h => absurd h (Nat.not_even_iff_odd.2 hs)⟩
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have h1 : (G.pS (.top t j)).rank = rankX D j :=
      rank_node G (X := .top j) (show j ≤ D.R.m by simp only [DefPair] at hp; omega) (fun j h => by cases h)
    rw [h1]
    exact (even_rankX D j).mul_right _

theorem fock_vac_eq_jets : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : ChiGrid.GridData L sc} (W : G.Weil)
    {U : Set T} (N : Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 →
    Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ p : Pair T, DefPair D.R.m p →
    ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS p).rank (G.pT p).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 →
    ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) f →
    ∃ c : ℂˣ, ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ,
      fockIn W N.frC p f (monomial k 1) 0 =
        c * opp p ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hc hδ ht0 p hp e0 he0 f hf
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    exact GlobalTheory.T.fockJets_origin_oppositeSignVacuum_conjPeriod W N δ t0 hc hδ ht0 i hi e0 he0 f hf
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j => exact GlobalTheory.T.fockJet_vacuum_eq_const_mul_periodScaledJet W N δ t0 hc hδ ht0 t j hp e0 he0 f hf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : ChiGrid.GridData L sc} (W : G.Weil)

open Classical in

theorem normal_nonempty : ∀ μ0, L.Is μ0 → ∀ (U : Set T) (N : Std G U), Nonempty (Normal W N) := by
  intro μ0 _ U N
  have hodd := GlobalTheory.Vacuum.exists_vacuum D
  obtain ⟨δ, hc, hδ⟩ := exists_delta D
  obtain ⟨t0, ht0⟩ := (GlobalTheory.TwoTorsionPt.exists_point D D.host.ccK δ hc).1
  let e0 : ∀ p : Pair T, Formalism.MainNotions.TaylorLogMetric.VC D (G.pS p).rank (G.pT p).rank → ℂ := fun p =>
    if h : Even ((G.pS p).rank * (G.pT p).rank) then Classical.choose (hodd D.host.ccK δ hc t0 ht0 _ _ h) else 0
  have e0_is : ∀ p, DefPair D.R.m p → Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ (e0 p) := fun p hp => by
    have h := even_rank_mul G p hp
    simp only [e0, dif_pos h]
    exact (Classical.choose_spec (hodd D.host.ccK δ hc t0 ht0 _ _ h)).1
  let vac : ∀ p : Pair T, WO (G.pS p) (G.pT p) → ℂ := fun p =>
    if h : ∃ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) f
    then Classical.choose h else 0
  have vac_is : ∀ p, DefPair D.R.m p →
      IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) (vac p) := fun p hp => by
    have h := GlobalTheory.T.exists_unitVacuum_standardLattices_definitePair W N p hp
    simp only [vac, dif_pos h]
    exact Classical.choose_spec h
  let c0 : Pair T → ℂˣ := fun p =>
    if h : ∃ c : ℂˣ, ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ,
      fockIn W N.frC p (vac p) (monomial k 1) 0 =
        c * opp p ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (monomial k 1) (e0 p))
    then Classical.choose h else 1
  have kernelNorm_constant_spec : ∀ p, DefPair D.R.m p → ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ,
      fockIn W N.frC p (vac p) (monomial k 1) 0 =
        c0 p * opp p ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (monomial k 1) (e0 p)) := by
    intro p hp k
    have h := fock_vac_eq_jets W N δ t0 hc hδ ht0 p hp (e0 p) (e0_is p hp) (vac p) (vac_is p hp)
    simp only [c0, dif_pos h]
    exact Classical.choose_spec h k
  exact ⟨⟨δ, hc, t0, ht0, e0, e0_is, vac, vac_is, c0, kernelNorm_constant_spec, fun t t' j => ⟨rfl, rfl, rfl⟩⟩⟩

theorem Normal.period_ne_zero {U : Set T} {N : Std G U} (Z : Normal W N) (τ : D.what₂.Tau) : period Z.δ τ ≠ 0 := by
  refine GlobalTheory.FunObj.period_ne_zero ?_ τ
  rintro h
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_one D D.host.ccK_ne_bot
  have e : Z.δ ^ 12 = Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK 1) := Z.crv.2
  rw [h] at e
  exact GlobalTheory.CurveLattice.discr_ne_zero _ L hL (by rw [← e]; simp)

end GlobalTheory.FunObj
