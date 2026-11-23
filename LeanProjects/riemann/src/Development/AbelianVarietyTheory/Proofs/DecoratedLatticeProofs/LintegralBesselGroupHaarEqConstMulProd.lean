import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CastGAMemGFset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Mi.BesHaar

open scoped NNReal ENNReal

noncomputable def prodEquiv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) :
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) ≃ₜ*
      besGrp B.d B.o where
  toFun p := ⟨(iotaX X h).symm ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)), by
    rw [((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _), ContinuousMulEquiv.apply_symm_apply]
    exact ⟨p.1.2, p.2.2⟩⟩
  invFun s := (⟨(iotaX X h s.1).1, (((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _).1 s.2).1⟩,
    ⟨(iotaX X h s.1).2, (((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _).1 s.2).2⟩)
  left_inv p := by
    ext <;> simp
  right_inv s := by
    ext
    simp
  map_mul' p q := by
    ext
    simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul]
    rw [← map_mul]
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ((iotaX X h).symm.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hc : Continuous (fun s : besGrp B.d B.o => iotaX X h s.1) :=
      (iotaX X h).continuous.comp continuous_subtype_val
    exact ((continuous_fst.comp hc).subtype_mk _).prodMk ((continuous_snd.comp hc).subtype_mk _)

theorem iota_prodEquiv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)
    (p : Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) :
    iotaX X h (prodEquiv X h B p).1 = ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)) := by
  show iotaX X h ((iotaX X h).symm _) = _
  simp

theorem lintegral_besGrp_eq : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))), μSf.IsHaarMeasure → SigmaFinite μSf → IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) → ∃ c : ℝ, 0 < c ∧ ∀ Φ : X.B.I.GA → ENNReal, Measurable Φ → ∫⁻ s, Φ (iotaX X h s.1) ∂B.lev.μR = ENNReal.ofReal c * ∫⁻ a, ∫⁻ t, Φ (a, t.1) ∂μSf ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X h u ψ A B μSf hSf hσf hS
  haveI := hSf
  haveI := hσf
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : LocallyCompactSpace X.B.I.GA := hR.1
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : SecondCountableTopology (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.secondCountableTopology
  haveI : LocallyCompactSpace (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hcl : IsClosed (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ B.d B.o
  haveI : LocallyCompactSpace (besGrp B.d B.o) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : B.lev.μR.IsHaarMeasure := (GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  have hSi : IsClosed ((Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u
  haveI : LocallyCompactSpace (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) := hSi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨hHaar', -, -⟩ := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) hSi _ hS
  haveI := hHaar'
  have hmap := Formalism.L2.SG.Pf.map_comap_subgroup (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) hSi _ hS.2.2.1
  set μS' := (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).comap ((↑) : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) → X.B.I.Ginf) with hμS'
  haveI : SigmaFinite μS' := inferInstance
  let e := GlobalTheory.Core.Mi.BesHaar.prodEquiv X h B
  haveI : LocallyCompactSpace ((Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : (B.lev.μR.map e.symm).IsHaarMeasure := e.symm.isHaarMeasure_map B.lev.μR
  haveI : (μS'.prod μSf).IsHaarMeasure := Measure.prod.instIsHaarMeasure μS' μSf
  have hcpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (B.lev.μR.map e.symm) (μS'.prod μSf)
  set c : ℝ≥0 := (B.lev.μR.map e.symm).haarScalarFactor (μS'.prod μSf) with hc
  have hme : Measurable (e : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) → besGrp B.d B.o) := e.continuous.measurable
  have hEq : B.lev.μR = (c • μS'.prod μSf).map e := by
    rw [hc, ← Measure.isMulLeftInvariant_eq_smul, Measure.map_map hme (show Measurable (e.symm : besGrp B.d B.o → (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))) from e.symm.continuous.measurable)]
    simp
  refine ⟨(c : ℝ), hcpos, fun Φ hΦ => ?_⟩
  have hv : Measurable (fun p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hΦ' : Measurable (fun p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => Φ ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf))) := hΦ.comp hv
  have hin : Measurable (fun a : X.B.I.Ginf => ∫⁻ t, Φ (a, (t : X.B.I.Gf)) ∂μSf) := by
    have : Measurable (Function.uncurry fun (a : X.B.I.Ginf) (t : Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => Φ (a, (t : X.B.I.Gf))) :=
      hΦ.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
    exact this.lintegral_prod_right'
  have hΦι : Measurable (fun s : besGrp B.d B.o => Φ (iotaX X h s.1)) :=
    hΦ.comp ((iotaX X h).continuous.measurable.comp measurable_subtype_coe)
  rw [hEq, lintegral_map hΦι hme]
  have hιe : ∀ p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), iotaX X h (e p).1 = ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)) :=
    GlobalTheory.Core.Mi.BesHaar.iota_prodEquiv X h B
  simp_rw [hιe]
  rw [lintegral_smul_measure, lintegral_prod _ hΦ'.aemeasurable, ← hmap,
    lintegral_map hin measurable_subtype_coe, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.Core.Mi.BesHaar
