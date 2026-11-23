import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryGroupModelsEquiv

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst)

namespace GlobalTheory.AdelicVol

theorem exists_fundamentalDomain_measure_eq (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund) :
    ∃ (μ : Measure (HA (AF I.F) I.cm.sig I.J)) (S : Set (HA (AF I.F) I.cm.sig I.J)), μ.IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF I.F) I.cm.sig I.J) S μ ∧ μ S = I.muA μf fund := by
  obtain ⟨-, -, T, hT, -, -⟩ := GlobalTheory.AdelicModels.exists_adelic_equiv I
  obtain ⟨Γ, hΓ, -, -, hdom⟩ := GlobalTheory.RatDiscrete.rational_points I
  have hF : IsFundamentalDomain Γ fund (I.muA μf) := hdom μf fund hfund
  haveI : BorelSpace (HA (AF I.F) I.cm.sig I.J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : IsTopologicalGroup (HA (AF I.F) I.cm.sig I.J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : SecondCountableTopology I.Gf := (GlobalTheory.CongTop.adelic_topology I).2.2.1
  haveI : BorelSpace I.GA := inferInstance
  haveI hG1 : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => inferInstance
  haveI hG2 : ∀ v, SigmaFinite (Formalism.REAL.muG (I.ε v)) := fun v => inferInstance
  haveI hP : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := inferInstance
  haveI hPs : SigmaFinite (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) := inferInstance
  haveI : (I.muA μf).IsHaarMeasure := by unfold AutInst.muA; infer_instance
  have hTm : Measurable T := T.continuous.measurable
  have hTsm : Measurable T.symm := T.symm.continuous.measurable
  let μ : Measure (HA (AF I.F) I.cm.sig I.J) := Measure.map T.symm (I.muA μf)
  haveI hμ : μ.IsHaarMeasure :=
    T.symm.toMulEquiv.isHaarMeasure_map (I.muA μf) T.symm.continuous T.continuous
  let e : Γ → HFinIn (AF I.F) I.cm.sig I.J := fun g =>
    ⟨T.symm g, (hT (T.symm g)).2 (by
      rw [ContinuousMulEquiv.apply_symm_apply, ← hΓ]
      exact g.2)⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply T.symm.injective
      exact congrArg Subtype.val hab
    · intro h
      have hm : T h.1 ∈ I.GFset := (hT h.1).1 h.2
      rw [← hΓ] at hm
      refine ⟨⟨T h.1, hm⟩, Subtype.ext ?_⟩
      exact T.symm_apply_apply _
  have hsc : ∀ g : Γ, Function.Semiconj T (fun x : HA (AF I.F) I.cm.sig I.J => e g • x) (fun y : I.GA => (g : I.GA) * y) := by
    intro g x
    show T ((T.symm (g : I.GA)) * x) = (g : I.GA) * T x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmp : MeasurePreserving T μ (I.muA μf) := by
    refine ⟨hTm, ?_⟩
    rw [Measure.map_map hTm hTsm]
    have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
    rw [this, Measure.map_id]
  refine ⟨μ, T ⁻¹' fund, hμ, hF.preimage_of_equiv hmp.quasiMeasurePreserving he hsc, ?_⟩
  rw [Measure.map_apply hTsm (hTm hfund.1), ← Set.preimage_comp]
  have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
  rw [this, Set.preimage_id]

theorem vol_finite_pos : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund → I.muA μf fund < ⊤ ∧ I.muA μf fund ≠ 0 ∧ 0 < I.vol μf fund := by
  intro I μf _ _ fund hfund
  obtain ⟨hcm, hJ, -⟩ := GlobalTheory.AdelicModels.exists_adelic_equiv I
  obtain ⟨μ, S, hμ, hS, hμS⟩ := exists_fundamentalDomain_measure_eq I μf fund hfund
  have hfin : μ S < ⊤ := GlobalTheory.Mem.VolFin.finVol I.F I.E I.cm.sig hcm I.n I.J hJ μ hμ S hS
  have hne : μ S ≠ 0 :=
    ((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary I.F I.E I.cm.sig I.n I.J μ hμ).2 S S hS hS).2
  rw [← hμS]
  refine ⟨hfin, hne, ?_⟩
  show 0 < ((I.muA μf) fund).toReal
  rw [← hμS]
  exact ENNReal.toReal_pos hne hfin.ne

end GlobalTheory.AdelicVol
