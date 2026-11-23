import Mathlib
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

noncomputable section

namespace GlobalTheory.BaseChain

open GlobalTheory.ChainOnto

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

def com : Com D where
  θ := (pk W).θ
  ψ := (pk W).ψ
  μ := (pk W).toLevCh.mu W.P.A3.A.μ0
  η := (pk W).eta
  Pg := (pk W).Pg
  P := lvP W
  chi := (pk W).chi

def cH : ENNReal := ((Nat.card (lvP W).H : ENNReal))⁻¹

def stageY (j : ℕ) : PiLocalization₂ D where
  V := Yc D j
  par := parB (Ptw D) (min j D.R.m)
  M := (pk W).MY j
  Λ := (pk W).ΛY j
  β := (pk W).βY j
  L := (pk W).datYt W.P.A3.A.μ0 j (lvP W)
  ν := cH W • (pk W).νY W.P.A3.A.μ0 j
  fd := (pk W).fdY W.P.A3.A.μ0 j

def stageX : PiLocalization₂ D where
  V := D.sp.X'
  par := parB (Ptw D) D.R.m
  M := (pk W).MX
  Λ := (pk W).ΛX
  β := (pk W).βX
  L := datXP (pk W) (lvP W) W.P.A3.A.μ0
  ν := cH W • (pk W).νX W.P.A3.A.μ0
  fd := (pk W).fdX W.P.A3.A.μ0

variable {W} {u : D.what₂.Word} (f : FamCh W u)

def stepY (j : ℕ) : Step (com W) (stageY W j) (stageY W (j + 1)) where
  ω := (pk W).ωY W.P.A3.A.μ0 j
  f := (f.row W.P.A3.A.μ0).vP j
  It := (pk W).ItY j
  io := (f.row W.P.A3.A.μ0).io j

def stepX (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : Step (com W) (stageY W (j + 1)) (stageX W) where
  ω := omT (pk W) W.P.A3.A.μ0 j h
  f := (f.row W.P.A3.A.μ0).vT j h
  It := f.c.ItT j h
  io := (f.row W.P.A3.A.μ0).ioT j h

end GlobalTheory.BaseChain

end
