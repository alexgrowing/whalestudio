import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTraceChi

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

abbrev reductionYZero (W : RealPack ex) (h : GA D (D.sp.Y 0)) : Formalism.L2.DIV.G0 (pk W).Pg D.R.r :=
  Formalism.L2.DIV.rTup ((pk W).βY 0) ((pk W).dat0 (lvP W)) (finE (Yc D 0) h)

theorem rChi_eq_chi (W : RealPack ex) {h : GA D (D.sp.Y 0)} (hh : h ∈ rJ W) :
    ∃ hg : reductionYZero W h ∈ (lvP W).H, rChi W h = (((lvP W).chi ⟨_, hg⟩ : ℂˣ) : ℂ) := by
  have h2 := hh.2
  have h3 := (Formalism.L2.DIV.mem_lev.1 h2).2
  refine ⟨h3, ?_⟩
  simp only [rChi, Formalism.IndefR.Lev.levChi, Formalism.L2.DIV.levFn]
  rw [Formalism.L2.DIV.extendOne_of_mem _ h3]
  simp [Formalism.IndefR.Links.LevCh.dat0, Formalism.IndefR.Lev.datY]
  rfl

end GlobalTheory.FamTraceChi

end
