import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.PlaceInj

theorem under_injective : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Function.Injective (fun i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP} => HeightOneSpectrum.under (𝓞 D.host.F) i.1) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have lev : (pk W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  rintro ⟨P, hP⟩ ⟨P', hP'⟩ h
  simp only at h
  apply Subtype.ext
  show P = P'

  have key : ∀ A B : Formalism.L2.DIV.Pl D.host.E, A ∈ (pk W).Pg → (B ∈ (pk W).Pg ∨ QAll W B) →
      A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → A = B := by
    intro A B hA hB hAB
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hAB.symm with e | e
    · exact e.symm
    · exfalso
      have hc : Formalism.IndefR.Lev.IsConjPl A B := GlobalTheory.GoodPrimes.isConjPl_iff.2 e
      rcases hB with hB | ⟨t, hB⟩
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev W.P.A3.A.μ0).1 A hA B (Or.inl hB) hc
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev t).1 A hA B (Or.inr hB) hc
  rcases hP with hP | hP
  · exact key P P' hP hP' h
  · rcases hP' with hP' | hP'
    · exact (key P' P hP' (Or.inr hP) h.symm).symm
    · exact hW.sel P P' hP hP' h

end GlobalTheory.Fam.PlaceInj
