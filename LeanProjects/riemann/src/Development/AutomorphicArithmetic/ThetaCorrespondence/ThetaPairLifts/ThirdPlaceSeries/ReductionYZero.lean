import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseLevelDatumLevelEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTraceChi
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev reductionYZero_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (h : GA D (D.sp.Y 0)) : Formalism.L2.DIV.G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r :=
  Formalism.L2.DIV.rTup ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).dat0 (_root_.GlobalTheory.Fam.complexLevelStructure W)) (finE (Yc D 0) h)
theorem rChi_eq_lvP_chi_of_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {h : GA D (D.sp.Y 0)} (hh : h ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    ∃ hg : _root_.GlobalTheory.FamTraceChi.reductionYZero_alt W h ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H, _root_.GlobalTheory.MiTop.realCharacter W h = (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hg⟩ : ℂˣ) : ℂ) := by
  have h2 := hh.2
  have h3 := (Formalism.L2.DIV.mem_lev.1 h2).2
  refine ⟨h3, ?_⟩
  simp only [_root_.GlobalTheory.MiTop.realCharacter, Formalism.IndefR.Lev.levChi, Formalism.L2.DIV.levFn]
  rw [Formalism.L2.DIV.extendOne_of_mem _ h3]
  simp [Formalism.IndefR.Links.LevCh.dat0, Formalism.IndefR.Lev.datY]
  rfl
end GlobalTheory.FamTraceChi
end
end
