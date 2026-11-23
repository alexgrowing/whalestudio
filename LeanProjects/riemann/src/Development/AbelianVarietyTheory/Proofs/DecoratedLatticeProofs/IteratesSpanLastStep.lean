import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMemKfin
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.SpanX

theorem itSpans_pk : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → GlobalTheory.Core.Mi.ItSpans ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).ItX := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W hP
  have hC := hP.bot.hyp.2.2.2.1
  have hok := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ _ hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX hC.chain.vY hC.chain.vX
  have hm : 0 < D.R.m := lt_of_lt_of_le two_pos D.R.two_le_m
  obtain ⟨hw, hv⟩ := hok.2 W.P.A3.A.μ0 ⟨D.R.m - 1, by omega⟩ rfl
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).θ (pk W).ψ _ _
    ((pk W).ωX W.P.A3.A.μ0) ((pk W).vX W.P.A3.A.μ0) (pk W).ItX hC.models.inf hw hv (hC.chain.ItX W.P.A3.A.μ0)
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap ((pk W).ItX P) (Submodule.span ℂ
      {x | ∃ (P : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (y : (pk W).MX.Vec), KVecP (pk W).MX y ∧
        x = (pk W).ItX P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => GlobalTheory.Core.Mi.StepSpans.isKFin_of_mem_kfin _ _ (hy τ), rfl⟩
  exact hu'

end GlobalTheory.Core.Mi.SpanX

end
