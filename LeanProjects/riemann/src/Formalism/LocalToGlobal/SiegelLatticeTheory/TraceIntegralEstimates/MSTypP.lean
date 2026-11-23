import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyMSLeaf
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSOrdP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolVFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieFD
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain

namespace Formalism.L2.S.Pv.MSTypP

open Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.Carrier.EnergyConst Formalism.L2.SG.Pf.Carrier.EnergyMS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem T_cong {D : D7} (u u' : D.what₂.Word) :
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] := by
  unfold Nat.ModEq Formalism.MainNotions.S.Lat.gS
  rw [D.T_mod_gg u, D.T_mod_gg u']

theorem dN_typed {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : PlX X) (hv : TypAt X v) : dN X v = 1 := by
  have h := Formalism.L2.SG.Pf.AlTieFD.different_generator_unit X ⟨v, hv⟩
  rw [Formalism.L2.SG.Pf.NcVal.absV_dV] at h
  have h2 : dN X v = (((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) : ℕ) : ℝ)⁻¹)⁻¹ := by
    rw [inv_inv]; rfl
  rw [h2, h, inv_one]

theorem msTyp_holds : MSTyp := by
  intro D X u u' ψ hψ hstd v hv hZ
  have h := Formalism.L2.SG.Pf.NcVal.volTypV_holds X u u' ψ hψ hstd (T_cong u u') v hv
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) = (gAt X v : ℝ) := by
    rw [(Formalism.L2.SG.Pf.gSplitX_holds X ⟨v, hv⟩).1]
  rw [dN_typed X v hv, one_pow, one_mul, hN, ← h, div_mul_cancel₀ _ hZ.ne']

theorem stepGSplit_holds : StepGSplit := fun D X => Formalism.L2.SG.Pf.gSplitX_holds X

theorem finrank_hostE' (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem degE_holds : DegE := fun D => finrank_hostE' D

theorem discEF_holds : DiscEF := by
  intro D X
  have hE : NumberField.discr X.B.I.E = NumberField.discr D.host.E :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.E X.ιE
  have hF : NumberField.discr X.B.I.F = NumberField.discr D.host.F :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.F (Formalism.L2.SG.Pf.DstarIdxPf.iF X)
  rw [hE, hF, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq]
  push_cast
  rw [abs_pow]

theorem gAt_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (p : TypX X) (i : Fin 2) :
    gAt X p.1 = D.host.g i ↔ ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  have hne := D.host.g_ne
  obtain ⟨j, hj⟩ := Formalism.L2.SG.Pf.AlTieFD.over_g_of_typed X p
  unfold gAt
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    split_ifs with h0
    · exact ⟨fun _ => h0, fun _ => rfl⟩
    · exact ⟨fun h => absurd h.symm hne, fun h => absurd h h0⟩
  · simp only [Fin.mk_one, Fin.isValue]
    split_ifs with h0
    · refine ⟨fun h => absurd h hne, fun h1 => ?_⟩
      exact (Formalism.L2.SG.Pf.AlTieFD.not_both X p.1 h0 h1).elim
    · refine ⟨fun _ => ?_, fun _ => rfl⟩
      fin_cases j
      · exact absurd hj h0
      · exact hj

theorem typCount_holds : TypCount := by
  intro D X i
  have hc := Formalism.L2.SG.Pf.DstarIdxPf.card_over X i
  rw [← hc, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  refine
    { toFun := fun p => ⟨p.1.1, (gAt_iff X p.1 i).1 (Finset.mem_filter.1 p.2).2⟩
      invFun := fun v => ⟨⟨v.1, ?_⟩, ?_⟩
      left_inv := fun p => rfl
      right_inv := fun v => rfl }
  · have hg0 := (D.host.g_prime 0).ne_zero
    have hg1 := (D.host.g_prime 1).ne_zero
    refine (mem_typSet X.B.I.F _ _ hg0 hg1 v.1).2 ?_
    fin_cases i
    · exact Or.inl v.2
    · exact Or.inr v.2
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact (gAt_iff X _ i).2 v.2

theorem lemmaMSStd_holds {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.Carrier.EnergyConst2.LemmaMSStd X u u' ψ :=
  lemmaMSStd_of_leaves Formalism.L2.S.Pv.MSOrdP.msOrd_holds msTyp_holds stepGSplit_holds typCount_holds discEF_holds
    degE_holds X u u' ψ

end Formalism.L2.S.Pv.MSTypP
