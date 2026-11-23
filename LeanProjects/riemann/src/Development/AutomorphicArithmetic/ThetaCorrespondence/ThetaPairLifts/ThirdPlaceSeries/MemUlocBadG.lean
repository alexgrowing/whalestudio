import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasure
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevelVLBaseStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InJRedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PatternOfTraceAtGStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace.AtG
set_option maxHeartbeats 1000000 in
theorem mem_Uloc_badG_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hIn v hv
  have hstd := hA.tr.std.some u
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 2, ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
    rcases hv with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨w, hw, -, hu, -⟩ := GlobalTheory.Mem.Col2.TC.GLev0.exists_w (_root_.GlobalTheory.MiTop.formsAtZero W u).gl hstd.gl.piG i0 v hi0
  have hwP : w ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg := (hA.lev.2.1 w).2 (GlobalTheory.Mem.Col2.TC.GLev0.mem_vGs.2 ⟨i0, hw⟩)
  obtain ⟨i, hi⟩ := a.pl.surjective ⟨w, hwP⟩
  have hqv : (a.G i).q.v = v := by
    rw [((ha.tie row col).2.idem i).2, hi]
    exact hu
  have hTv : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal :=
    GlobalTheory.Mem.Col2.TC.GLev0.T_notMem X u i0 hi0
  have hx := _root_.GlobalTheory.T.true_geometry_compact_level_property_alt W hA u a hat κ hκ y hy hIn.1 v hTv
  have hfr : (_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.fr i0 v hi0 = 1 := hstd.fr0 i0 v hi0
  refine ((_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.mem i0 v hi0 _ hx).2 ?_
  rw [hfr]
  exact _root_.GlobalTheory.T.true_geometry_final_index_alt W hA u a ha hat row col hc κ hκ y hy i v i0 hi0 hqv (_root_.GlobalTheory.T.true_geometry_final_measure_alt W hA u a ha hat κ hIn.2.2 i)
end GlobalTheory.FamTrace.AtG
end
