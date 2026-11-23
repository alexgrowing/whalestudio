import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetcutA
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.BeConjOfNormHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FormalGroupLawFirstHalfHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulByIntegralIsClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FstMemClosureNatCast
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PhAtMulByNorm
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMEndo

section Series
open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ : Type*}

theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  obtain ⟨-, -, h0, h1⟩ := h
  have hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => const_l g
  have he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => h0
  have h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p]))
      (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i := fun _ => h1
  have h3 := GlobalTheory.FormalInv.eq_substInv_of_right hl he h2
  have h4 := GlobalTheory.FormalInv.subst_substInv_left hl
    (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()
  rw [← h3] at h4
  exact h4

theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

theorem constantCoeff_subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, map_mul, ha, zero_mul]

theorem constantCoeff_lg {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.lg a) = 0 :=
  constantCoeff_subst_zero (const_l g) ha

theorem constantCoeff_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.pt a) = 0 :=
  constantCoeff_subst_zero h.2.2.1 ha

theorem lg_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.pt a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [G1.lg, G1.pt, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' h.2.2.1) ha', h.2.2.2, PowerSeries.subst_X ha']

theorem lg_mulBy (h : g.Ok) (c : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.mulBy c a) = MvPowerSeries.C c * g.lg a := by
  rw [G1.mulBy, lg_pt g h]
  rw [map_mul, constantCoeff_lg g ha, mul_zero]

theorem mulBy_add (h : g.Ok) (c c' : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.mulBy (c + c') a = g.add (g.mulBy c a) (g.mulBy c' a) := by
  rw [G1.add, lg_mulBy g h c ha, lg_mulBy g h c' ha, G1.mulBy, map_add, add_mul]

theorem add_eq_subst (h : g.Ok) (A B : MvPowerSeries σ ℂ_[p]) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    g.add A B = MvPowerSeries.subst ![A, B] (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
  have hab : MvPowerSeries.HasSubst ![A, B] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hA, hB])
  have hs : MvPowerSeries.constantCoeff (g.lg (Xv 0) + g.lg (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add, constantCoeff_lg g (MvPowerSeries.constantCoeff_X _),
      constantCoeff_lg g (MvPowerSeries.constantCoeff_X _), add_zero]
  have hsl : ∀ i : Fin 2, MvPowerSeries.subst ![A, B] (g.lg (Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) =
      g.lg (![A, B] i) := by
    intro i
    have hX : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)
    rw [G1.lg, G1.lg, PowerSeries.subst, PowerSeries.subst,
      MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X i)) hab]
    congr 1
    funext _
    exact MvPowerSeries.subst_X hab i
  rw [G1.add, G1.add, G1.pt, G1.pt, PowerSeries.subst, PowerSeries.subst,
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hs)) hab]
  congr 1
  funext _
  rw [MvPowerSeries.subst_add hab, hsl 0, hsl 1]
  rfl

theorem integralMv_zero : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := fun n => by
  simp [IsIntP]

theorem integralMv_X (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := fun n => by
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem integral_mulBy_semiring : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok →
    IntegralMv (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    IntegralMv (g.mulBy 0 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    IntegralMv (g.mulBy 1 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    ∀ c c' : ℂ_[p], IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy c' (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy (c + c') (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  intro p _ g h hadd
  have hX : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X _
  refine ⟨?_, ?_, ?_⟩
  · rw [mulBy_zero g h]; exact integralMv_zero
  · rw [mulBy_one g h]; exact integralMv_X ()
  · intro c c' hc hc'
    have h0 : ∀ d : ℂ_[p], MvPowerSeries.constantCoeff (g.mulBy d (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
      fun d => constantCoeff_pt g h (by rw [map_mul, constantCoeff_lg g hX, mul_zero])
    rw [mulBy_add g h c c' hX, add_eq_subst g h _ _ (h0 c) (h0 c')]
    exact ReciprocityTheory.ChartRestriction.L1.integralMv_subst2 (fun d => hadd d)
      (fun i => by fin_cases i <;> simp [h0]) (fun i => by
        fin_cases i
        · exact fun d => hc d
        · exact fun d => hc' d)

end Series

theorem endInt_all (D : D7) : GL3Theta.endInt D := by
  intro p _ cc δ g hA α hα
  have hok : g.Ok := hA.2.2.2.2
  have hadd := ((GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1 p cc δ g hA).1
  obtain ⟨h0, h1, hplus⟩ := integral_mulBy_semiring p g hok hadd
  set S : Set ℂ_[p] := {c | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} with hS
  have hcl : IsClosed S := GlobalTheory.mulBy_integral_isClosed p g
  have hnat : ∀ n : ℕ, (n : ℂ_[p]) ∈ S := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero]; exact h0
    | succ n ih =>
      rw [Nat.cast_succ]; exact hplus _ _ ih h1
  by_cases hp : p = 2
  · subst hp
    have h2 := GlobalTheory.TwoAdicFirst.fst_mem_closure_natCast D g.lam α hα
    have hsub : closure (Set.range (Nat.cast : ℕ → ℂ_[2])) ⊆ S :=
      closure_minimal (by rintro _ ⟨n, rfl⟩; exact hnat n) hcl
    exact hsub h2
  · obtain ⟨β, hβ, γ, hγ, hb1, hb2, hc1, hc2, rfl⟩ := Formalism.MainNotions.Ext.CutA.okpTwoUnits2_holds D p g.lam hp α hα
    have hunit : ∀ β ∈ GL3Theta.OKp D g.lam, ‖β.1‖ = 1 → ‖β.2‖ = 1 → β.1 ∈ S := by
      intro β hβ h1 h2
      have hc := Formalism.MainNotions.Ext.CutA.okpUnitsDense_holds D p g.lam hp β hβ h1 h2
      have hm := map_mem_closure continuous_fst hc (t := S) (by
        rintro _ ⟨a, ha, rfl⟩
        exact GlobalTheory.CMUnit.unit_endo D p cc δ g hA hp a ha)
      rwa [hcl.closure_eq] at hm
    exact hplus _ _ (hunit β hβ hb1 hb2) (hunit γ hγ hc1 hc2)

theorem endo_all : ∀ D : D7, GL3Theta.endInt D ∧ GL3Theta.phNorm D ∧ GL3Theta.beConj D := by
  intro D
  have he := endInt_all D
  have ha := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1
  have hB := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.2
  have hok : Formalism.MainNotions.Ext.CutA.PhNormOK D := GlobalTheory.CMNormPhi.phAt_mulBy_norm D he ha
  have hn := Formalism.MainNotions.Ext.CutA.phNorm_of' Formalism.MainNotions.Ext.CutA.phNormOfUnits_holds Formalism.MainNotions.Ext.CutA.phNormClosed_holds D hok he ha hB
  exact ⟨he, hn, Formalism.MainNotions.Ext.CutA.beConj_of' Formalism.MainNotions.Ext.CutA.beConjOfNorm_holds D he ha hn hB⟩

end GlobalTheory.CMEndo
