import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsCountBase

open Finset Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

open Formalism.MainNotions.BridgeLemma NumberField in
theorem splits_X (k : Fin 2) : SplitsCompl X.B.I.E (D.host.g k) := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  exact Formalism.L2.SG.ThmSOwn.splitsCompl_of_equiv X.ιE hspl

theorem hc_X (hT : AutTie D X.B X.pl) (v : NumberField.InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam v) := by
  exact Inh.aut_isHCParam_of_autTie hT v

theorem countBase_of (hT : AutTie D X.B X.pl) {large₂ : SizeData₂ D} {n0 : ℕ} {A C cb : ℝ}
    (hp : AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n0 A C cb) (hg1 : 4 * D.R.r < D.host.g 1) : CountBase X n0 A C cb := by
  obtain ⟨-, p2, p3, p4, p5, p6, p7, -, p9, p10, p11, p12⟩ := hp
  have hn := hT.n_eq
  have hf := hT.f_eq
  have hrd := hT.rd_eq
  have tg := X.g_eq
  have hq : ∀ v, X.B.I.pAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = true).card ∧
      X.B.I.qAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = false).card := by
    intro v
    have he := hT.eps_eq v
    constructor
    · simp only [AutInst.pAt, he]
      exact card_cast hn (fun a => epsS D.R a = true)
    · simp only [AutInst.qAt, he]
      exact card_cast hn (fun a => epsS D.R a = false)
  refine ⟨large₂.sc.b, C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE), fun k => ?_,
    fun v a c hac => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hn]; exact p2, ⟨_, _, hq, ?_⟩, p11, ?_, hc_X X hT, ?_, ?_, ?_, D.host.g_prime _, ?_, splits_X X _⟩
    · rw [hn]
      exact le_trans (Nat.pow_le_pow_left card_epsS_false 2) p3
    · rw [hrd, hn]; exact p4
    · intro v a
      rw [hT.lam_eq v a]; exact p5 _ _
    · rw [tg]
      exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    · rw [tg]
      have : gg D = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by unfold gg; push_cast; ring
      rw [← this]; exact p6
    · rw [hn]
      fin_cases k
      · exact hg1
      · exact p7
  · rw [hT.lam_eq v a, hT.lam_eq v c]
    exact p9 _ _ _ (by rw [← hT.eps_eq v a, ← hT.eps_eq v c]; exact hac)
  · rw [hn, hf, hrd]
  · rw [hf, hn]; exact p10
  · rw [hf, hn]; exact p12
  · have h := Formalism.MainNotions.BridgeLemma.Dstar_pos D
    rw [hT.Dstar_eq] at h
    exact h

theorem countBase_of_hyp (hT : AutTie D X.B X.pl) {L : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} {n0 : ℕ}
    {A C cb7 : ℝ} (hC : 0 ≤ C) (hcb : 0 < cb7) (hA : 2 * Cg ≤ A) (hn0 : (n0 : ℝ) ≤ D.R.k) (hCl2 : 2 ≤ Cl)
    (hCl3 : 2 * C ≤ Cl) (hll : Real.log L.sc.L ≤ cb7 * D.R.k) (hh : AdmissibleBoundsFromSource.hyp D L C0 C' Cl Cg cb Cu cT CT) :
    CountBase X n0 A C cb7 := by
  have hp := count_parameters_of_hyp L C0 C' Cl Cg cb Cu cT CT n0 A C cb7 hC hcb hA hn0 hCl2 hCl3 hll hh
  refine countBase_of X hT hp ?_
  obtain ⟨-, hH, -⟩ := hh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ContinuousCyclotomicCharacter₂, -⟩ := hH
  have hk5 := Formalism.MainNotions.S.five_le_k (D := D)
  have hb2 := Formalism.MainNotions.S.two_le_scb L
  have h5 : (4 : ℝ) * D.R.r < D.host.g 1 := Formalism.MainNotions.S.four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) Formalism.MainNotions.S.r_le_two_k ContinuousCyclotomicCharacter₂
  exact_mod_cast h5

section Fam

open Formalism.MainNotions.S.CountE Formalism.MainNotions.PlaceDegreeData Formalism.L2.SG.ThmSOwn

variable {eps : ℝ} (Fm : FamP eps)

theorem countBaseOwn (C0 : ℝ) (n0 : ℕ) (A C cb7 : ℝ) (hC : 0 ≤ C) (hcb : 0 < cb7)
    (hA : 2 * (Fm.CYL + 1) ≤ A) (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm) :
    HypOwn Fm C0 fun D L => ∀ X : HidaSetting D, AutTie D X.B X.pl → CountBase X n0 A C cb7 := by
  have hG := cGam_pos Fm
  obtain ⟨Y1, hY1, HY1⟩ := linear_le_pow_eight_eventually (8 * Fm.CGam) n0 (by positivity)
  obtain ⟨Y2, -, HY2⟩ := linear_le_pow_eight_eventually (cb7 * (8 * Fm.CGam)) 8 (by positivity)
  obtain ⟨x4, hx4⟩ := ev_y Fm (max Y1 Y2)
  refine ⟨max (Fm.x1 + 1) x4, fun x hx i hh X hT => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hx
    linarith
  have hy := hx4 x (le_trans (le_max_right _ _) hx)
  set y : ℝ := x ^ (eps / 8) with hydef
  have hy1 : 1 ≤ y := le_trans hY1 (le_trans (le_max_left _ _) hy)
  have a1 := HY1 y (le_trans (le_max_left _ _) hy)
  have a2 := HY2 y (le_trans (le_max_right _ _) hy)
  have hL := scL_eq Fm x hx1 i
  have hk8 := k_ge_of_hyp (Fm.L x i) hh
  rw [hL, Fm.CGam_eq x i] at hk8
  refine countBase_of_hyp X hT hC hcb hA ?_ hCl2 hCl3 ?_ hh
  · have : (n0 : ℝ) ≤ n0 * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    linarith
  · rw [hL, Real.log_pow]
    have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
    have h2 : cb7 * (8 * Fm.CGam * y ^ 8) ≤ cb7 * ((Fm.D x i).R.k : ℝ) := mul_le_mul_of_nonneg_left hk8 hcb.le
    push_cast
    nlinarith

end Fam

end Formalism.L2.SG.Pf.AllRowsCountBase
