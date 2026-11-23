import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CastGAMemGFset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Unfold

theorem lintegral_unfold : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ f : X.B.I.GA → ENNReal, Measurable f → ∫⁻ s, f (iotaX X h s.1) ∂B.lev.μR = ∫⁻ s in 𝓢, ∑' σ : Srat X u, f ((σ : X.B.I.GA) * iotaX X h s.1) ∂B.lev.μR := by
  intro D X h u ψ A B 𝓢 h𝓢 f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (D.sp.Y 0).gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig (D.sp.Y 0).gram
  have hH : B.lev.μR.IsHaarMeasure := (GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  have hgrp := (GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).2
  have : Countable (GQ (D.sp.Y 0)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (D.sp.Y 0).gram
  have : Countable ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) := Function.Injective.countable
    (f := fun x : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o) => (⟨x.1.1, x.2⟩ : GQ (D.sp.Y 0))) fun a b e =>
      Subtype.ext (Subtype.ext (congrArg (Subtype.val : GQ (D.sp.Y 0) → GA D (D.sp.Y 0)) e))
  have : SMulInvariantMeasure ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) (besGrp B.d B.o) B.lev.μR :=
    ⟨fun γ S _ => by
      show B.lev.μR ((fun y => (γ : besGrp B.d B.o) * y) ⁻¹' S) = B.lev.μR S
      exact measure_preimage_mul _ (γ : besGrp B.d B.o) S⟩
  have hιm : Measurable (fun s : besGrp B.d B.o => f (iotaX X h s.1)) :=
    hf.comp ((iotaX X h).continuous.measurable.comp measurable_subtype_coe)
  rw [h𝓢.lintegral_eq_tsum'' (fun s => f (iotaX X h s.1))]
  rw [← lintegral_tsum (f := fun (γ : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) (x : besGrp B.d B.o) => f (iotaX X h (γ • x).1))
    (fun γ => (hιm.comp (measurable_const_smul γ)).aemeasurable)]
  refine lintegral_congr fun s => ?_
  let e : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o) ≃ Srat X u := Equiv.ofBijective
    (fun γ => ⟨iotaX X h γ.1.1, (hgrp _).1 ⟨Subgroup.mem_subgroupOf.1 γ.2, γ.1.2⟩⟩)
    ⟨fun a b e => Subtype.ext (Subtype.ext ((iotaX X h).injective (congrArg Subtype.val e))), fun σ => by
      have hm := (hgrp ((iotaX X h).symm σ)).2 (by simpa using σ.2)
      exact ⟨⟨⟨_, hm.2⟩, Subgroup.mem_subgroupOf.2 hm.1⟩, Subtype.ext (by simp)⟩⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun γ => ?_
  show f (iotaX X h ((γ : besGrp B.d B.o) * s).1) = f (iotaX X h γ.1.1 * iotaX X h s.1)
  rw [Subgroup.coe_mul, map_mul]

end GlobalTheory.Core.Mi.Unfold
