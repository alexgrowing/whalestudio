import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesTypeNormsPrincipal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolume
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCorePb

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

theorem exists_laws_at_stages : ∀ X : GlobalTheory.Mem.Stages, (∀ W, X.toD7.vol W = GlobalTheory.Mem.Vol.trueVol X.toD7.sp.cm (tauE X.toD7) X.toD7.cd W) → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 X.toD7.host.K), (∀ k, ((X.toD7.host.g k : ℕ) : 𝓞 X.toD7.host.K) ∈ (pb k).asIdeal) → VolTieG X.toD7 ∧ OKPsi X.toD7 ∧ ∃ (T : CoreJ X.toD7) (_ : Algebra T.Q.c.F X.toD7.what₂.LL), LawsJ T ∧ LawsCore T.toCore ∧ T.Q.Canon ∧ T.pb = pb ∧ AlgTie T ∧ ∀ x, X.toD7.embE x ∈ (algebraMap T.Q.c.F X.toD7.what₂.LL).range := by
  intro X hv pb hg
  have hV : VolTieG X.toD7 := GlobalTheory.Mem.Vol.volTieG_of_trueVol X.toD7 hv
  refine ⟨hV, GlobalTheory.Mem.TypeNormPin.hermitianCodeWordStages_typeNorms_principal X, ?_⟩
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := GlobalTheory.Member.CoreExist.exists_core_pb X.toD7 (GlobalTheory.Mem.hermitianCodeWordStages_ringOfIntegers_full X)
    (GlobalTheory.Mem.hermitianCodeWordStages_has_rootOfUnity X) hV pb hg
  have hp : T.Q.PinField := h₁.pins.2.2.1
  letI := algTop T hp
  have ha : AlgTie T := algTie_algTop T hp
  refine ⟨T, algTop T hp, h₁, h₂, h₃, h₄, ha, fun x => ⟨embF T.Q.c X.toD7.host.φ₀ x, ?_⟩⟩
  apply X.toD7.what₂.embLL.injective
  exact (RingHom.congr_fun (res_embLL T ha hp) (embF T.Q.c X.toD7.host.φ₀ x)).trans
    (RingHom.congr_fun X.toD7.embE_φ₀ x).symm

end GlobalTheory.RealGeo
