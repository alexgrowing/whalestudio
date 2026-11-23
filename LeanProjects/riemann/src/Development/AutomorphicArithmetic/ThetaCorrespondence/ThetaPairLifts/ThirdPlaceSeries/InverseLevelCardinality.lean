import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
open GlobalTheory.ChainOnto
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def com_z : Com D where
  θ := (_root_.GlobalTheory.Fam.pk_z W).θ
  ψ := (_root_.GlobalTheory.Fam.pk_z W).ψ
  μ := (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0
  η := (_root_.GlobalTheory.Fam.pk_z W).eta
  Pg := (_root_.GlobalTheory.Fam.pk_z W).Pg
  P := _root_.GlobalTheory.Fam.complexLevelStructure W
  chi := (_root_.GlobalTheory.Fam.pk_z W).chi
def inverseLevelCardinality : ENNReal := ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ENNReal))⁻¹
def stageOfSpaceY (j : ℕ) : PiLocalization₂ D where
  V := Yc D j
  par := parB (Ptw D) (min j D.R.m)
  M := (_root_.GlobalTheory.Fam.pk_z W).MY j
  Λ := (_root_.GlobalTheory.Fam.pk_z W).ΛY j
  β := (_root_.GlobalTheory.Fam.pk_z W).βY j
  L := (_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 j (_root_.GlobalTheory.Fam.complexLevelStructure W)
  ν := _root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j
  fd := (_root_.GlobalTheory.Fam.pk_z W).fdY W.P.A3.A.μ0 j
def stageOfSpaceX : PiLocalization₂ D where
  V := D.sp.X'
  par := parB (Ptw D) D.R.m
  M := (_root_.GlobalTheory.Fam.pk_z W).MX
  Λ := (_root_.GlobalTheory.Fam.pk_z W).ΛX
  β := (_root_.GlobalTheory.Fam.pk_z W).βX
  L := datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0
  ν := _root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0
  fd := (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
def transitionBetweenSpacesY (j : ℕ) : Step (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)) where
  ω := (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j
  f := (f.row W.P.A3.A.μ0).vP j
  It := (_root_.GlobalTheory.Fam.pk_z W).ItY j
  io := (f.row W.P.A3.A.μ0).io j
def transitionToSpaceX (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : Step (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)) (_root_.GlobalTheory.BaseChain.stageOfSpaceX W) where
  ω := omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h
  f := (f.row W.P.A3.A.μ0).vT j h
  It := f.c.ItT j h
  io := (f.row W.P.A3.A.μ0).ioT j h
end GlobalTheory.BaseChain
end
end
