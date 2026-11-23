import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ConjugationInvariantMeasure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MuSHaar

open scoped Pointwise

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Sinf Formalism.L2.SG.PoincareInHH.PoincareSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

theorem muN_conj (h : X.B.I.Ginf) (hh : h ∈ Hinf X u) :
    (X.muN u).map (fun x => h * x * h⁻¹) = X.muN u := by
  have hNc : IsClosed (X.NinfU u) := isClosed_ninfU X u
  have hHc : IsCompact ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := hinf_compact X u
  obtain ⟨-, hfin, hpos⟩ := haarOnSet_isHaar_inst X.B.I (NinfSub X.eR (X.zR u)) (isClosed_ninfU X u)
    (X.muN u) (X.muN_haar u)
  have hgN : QPK.IsGrp (X.NinfU u) :=
    ⟨(NinfSub X.eR (X.zR u)).one_mem, fun a ha b hb => (NinfSub X.eR (X.zR u)).mul_mem ha hb,
      fun a ha => (NinfSub X.eR (X.zR u)).inv_mem ha⟩
  have hgH : QPK.IsGrp ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) :=
    ⟨(Hinf X u).one_mem, fun a ha b hb => (Hinf X u).mul_mem ha hb, fun a ha => (Hinf X u).inv_mem ha⟩
  exact QPK.conjugation_invariant_measure X.B.I.Ginf (X.NinfU u) _ hNc hHc hgN hgH
    (fun h hh m hm => conj_ninf X u hh hm) (X.muN u) (X.muN_haar u) ⟨fun K hK => hfin K hK⟩
    (fun U hU hne => (hpos U hU hne).ne') h hh

theorem muS_compact {K : Set X.B.I.Ginf} (hK : IsCompact K) :
    ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) K < ⊤ := by
  haveI := (X.muN_haar u).1
  haveI := (X.muH_haar u).1
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  set L : Set X.B.I.Ginf := (K * ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)⁻¹) ∩ X.NinfU u with hL
  have hLc : IsCompact L := (hK.mul (hinf_compact X u).inv).inter_right (isClosed_ninfU X u)
  rw [Measure.map_apply hmul hK.isClosed.measurableSet]
  calc ((X.muN u).prod (X.muH u)) ((fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) ⁻¹' K)
      ≤ ((X.muN u).prod (X.muH u)) (L ×ˢ Set.univ) := by
        refine measure_mono_ae ?_
        filter_upwards [ae_NH X u] with p hp hpK
        refine ⟨⟨?_, hp.1⟩, Set.mem_univ _⟩
        have e : p.1 = (p.1 * p.2) * p.2⁻¹ := by group
        rw [e]
        exact Set.mul_mem_mul hpK (Set.inv_mem_inv.2 hp.2)
    _ = X.muN u L * X.muH u Set.univ := Measure.prod_prod _ _
    _ < ⊤ := ENNReal.mul_lt_top (muN_compact X u hLc) (hFinite_holds X u)

theorem muS_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X u
  obtain ⟨hNσ, hN0, -, hNinv⟩ := X.muN_haar u
  obtain ⟨hHσ, hH0, -, hHinv⟩ := X.muH_haar u
  haveI := hNσ
  haveI := hHσ
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI : IsFiniteMeasureOnCompacts (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) :=
      ⟨fun K hK => muS_compact X u hK⟩
    infer_instance
  · intro h0
    have h1 := congrArg (fun μ : Measure X.B.I.Ginf => μ Set.univ) h0
    simp only [Measure.map_apply hmul MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply] at h1
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero,
      Measure.measure_univ_eq_zero] at h1
    exact h1.elim hN0 hH0
  · exact ae_iff.1 (Formalism.L2.SG.WuDecayPf.muSOn X u)
  · intro s hs
    obtain ⟨h0, hh0, n0, hn0, rfl⟩ := levi X u hs
    have hf : (X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹) = X.muN u := by
      have e : (fun x => h0 * (n0 * x) * h0⁻¹) = (fun x => h0 * x * h0⁻¹) ∘ (fun x => n0 * x) := rfl
      rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), hNinv n0 hn0, muN_conj X u h0 hh0]
    have hg : (X.muH u).map (fun y => h0 * y) = X.muH u := hHinv h0 hh0
    have hfm : Measurable (fun x : X.B.I.Ginf => h0 * (n0 * x) * h0⁻¹) := by fun_prop
    have hgm : Measurable (fun y : X.B.I.Ginf => h0 * y) := by fun_prop
    calc (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).map (fun x => h0 * n0 * x)
        = ((X.muN u).prod (X.muH u)).map ((fun x => h0 * n0 * x) ∘ (fun p => p.1 * p.2)) :=
          Measure.map_map (by fun_prop) hmul
      _ = ((X.muN u).prod (X.muH u)).map ((fun p => p.1 * p.2) ∘
            Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y)) := by
          congr 1; funext p; simp only [Function.comp, Prod.map]; group
      _ = (((X.muN u).prod (X.muH u)).map
            (Prod.map (fun x => h0 * (n0 * x) * h0⁻¹) (fun y => h0 * y))).map (fun p => p.1 * p.2) :=
          (Measure.map_map hmul (hfm.prodMap hgm)).symm
      _ = (((X.muN u).map (fun x => h0 * (n0 * x) * h0⁻¹)).prod ((X.muH u).map (fun y => h0 * y))).map
            (fun p => p.1 * p.2) := by rw [Measure.map_prod_map _ _ hfm hgm]
      _ = ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) := by rw [hf, hg]

end GlobalTheory.MuSHaar
