import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLevelSpherical
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevSph
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol
theorem levSph_bT_compact_open_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ≤ GfC _ ∧ IsCompact (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) ∧ IsOpen (((_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT).subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _
  have hx : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ha.top.2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig (I.rec7 l Z).sp.X'.gram
  have hmem : ∀ h, h ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ↔
      a.g.bT⁻¹ * h * a.g.bT ∈ Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) := fun h => _root_.GlobalTheory.TopVol.mem_level_sphere_iff_conj_mem_levS h
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    have h1 : a.g.bT⁻¹ * h * a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ((hmem h).1 hh).1
    have h2 : h = a.g.bT * (a.g.bT⁻¹ * h * a.g.bT) * a.g.bT⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hx h1) (inv_mem hx)
  · have he : (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) =
        (fun k => a.g.bT * k * a.g.bT⁻¹) '' (Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) : Set _) := by
      ext h
      constructor
      · intro hh
        exact ⟨_, (hmem h).1 hh, by group⟩
      · rintro ⟨k, hk, rfl⟩
        refine (hmem _).2 ?_
        have : a.g.bT⁻¹ * (a.g.bT * k * a.g.bT⁻¹) * a.g.bT = k := by group
        rw [this]; exact hk
    rw [he]
    exact (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _).image (by fun_prop)
  · have ho := GlobalTheory.ParahoricCompact.isOpen_comap_lev _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W)
    have hc : Continuous fun k : GfC (I.rec7 l Z).sp.X' => a.g.bT⁻¹ * (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') * a.g.bT := by
      fun_prop
    convert ho.preimage hc using 1
    ext k
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    rw [hmem]
    constructor
    · intro hk; exact hk.2
    · intro hk
      exact ⟨(GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').inv_mem hx) k.2) hx, hk⟩
end GlobalTheory.TopVol
end
end
