import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentAtSplitPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CondUnifStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QGeoAt
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.QGeoAt
open GlobalTheory.QGeoAt in
theorem GlobalTheory.QGeoAt.geo_of_frames_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b))), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), _root_.GlobalTheory.Fam.QAllAlt W PP → ∀ (l : LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP), LocY l y v.N (_root_.GlobalTheory.Fam.pk_z W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b v hv hτ hNT PP hPP l hY hFX hFT
  obtain ⟨⟨ψk, hchar, hcond⟩, ⟨ν, hν⟩, hϖ⟩ := _root_.GlobalTheory.T.local_character_conductor_one_exists_alt W u hW a PP (Or.inr hPP) l
  obtain ⟨ϖ, hunif, hcompl⟩ := hϖ hPP
  refine ⟨{
    k := l.k
    ν := ν
    unitVol := hν
    q := l.q
    idem := l.idem
    unit := l.unit
    ψk := ψk
    char := hchar
    cond := hcond
    ϖ := ϖ
    unif := hunif
    compl := hcompl
    s := l.s
    hs := l.hs
    FX := l.FX
    FT := l.FT
    FM := l.FM
    FY := hY.FY
    sc := hY.sc
    sc_ne := fun j h => by simpa [h] using hY.sc_unit j
    sc_step := hY.sc_step
    bes := hY.bes
    jac := hY.jac
    z₀ := fun r => (ofSplit l.q).pr (a.ζ₀ r)
    last := l.last
    tau := fun h => by rw [hτ]; exact hY.tau h
    latX := l.latX
    latM := l.latM
    latY := hY.latY
    latT := by rw [hNT]; exact l.latT
    gl := fun j d hd => glOf (ofSplit l.q) _ (hY.FY j d hd)
    gl_loc := fun j d hd g => glOf_loc (ofSplit l.q) _ (hY.FY j d hd) g
    frame := fun j d hd => by
      obtain ⟨e, he, hm⟩ := hY.frame j d hd
      refine ⟨e, he, ?_⟩
      simpa using hm
    frameTop := l.frameTop }, hFX, hFT, rfl⟩
end
