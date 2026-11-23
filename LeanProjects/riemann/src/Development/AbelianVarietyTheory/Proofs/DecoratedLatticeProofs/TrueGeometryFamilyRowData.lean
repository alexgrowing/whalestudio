import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralBottomDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyColumnDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkDownwardStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkOntoStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConsistentRowChoicesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinkZeroOfChartZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyRowsColumnsValidStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

theorem famAllQ_of_allTrue : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → 1 ≤ B.R.rS → GlobalTheory.ChainOnto.OntoAll (I.rec7 l Z) → FamAllQ W := by
  intro hCD hDS hHC hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hA hr ho
  have hpk := hA.pk
  obtain ⟨z, hzC, hzZ, hz⟩ := GlobalTheory.T.exists_central_bottom_datum W hpk hr
  refine ⟨z, hzC, hzZ, fun u => ?_⟩
  obtain ⟨a, haI, haT, haO, haF⟩ := GlobalTheory.T.all_true_family_datum hDS hHC hSA W hA u
  obtain ⟨row, hrI, hrS⟩ := GlobalTheory.T.exists_consistent_row_choices hCD W u hpk a.g
  have hcol := fun k => GlobalTheory.T.true_geometry_family_invariance hDS hHC W hA u a haI haT haO k row hrI hrS
  obtain ⟨col, hOK, hLaws, hCZ, hTail, hComm, hRat⟩ :=
    GlobalTheory.T.true_geometry_family_column_data hDS hHC hSA W hA u a haI haT row hrI hrS hcol
  have hc : (a.fam row col).c.Is := (GlobalTheory.T.family_rows_columns_valid hDS hHC W u hpk (a.fam row col) hOK).1
  have hPl := GlobalTheory.T.true_geometry_family_property W hA u a haI haT row col hc
  obtain ⟨d, hdB, hdb, hdz⟩ := hz u (a.fam row col) a.d.B hPl haF
  refine ⟨a.fam row col, d, hdz, hLaws, ?_, hTail, GlobalTheory.T.family_link_downward W u hpk _ hOK, GlobalTheory.T.family_link_onto W u hpk ho _ hOK, hComm, hRat⟩
  refine GlobalTheory.T.link_zero_of_chart_zero W u (a.fam row col) d hCZ (fun h₀ => ?_) hdb
  rw [hdB]
  exact haI.bot.1 h₀

end GlobalTheory.MiTop
