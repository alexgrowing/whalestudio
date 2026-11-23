import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowColumnEntry
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamCol

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem zero_forms_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col t (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) ι w c₀, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) c₀ A ι w → (∀ β, A.kb 0 β = TC.kStd X u (B.R.N 0)) → ∀ α, (∀ φ, _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ ∈ ((a.fam row col).t t).Ram 0 ∧ ∀ y, ((a.fam row col).t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) y = (GlobalTheory.Core.Mi.chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ ((I.rec7 l Z).eMu u φ).1 y) ∧ ∀ ψ ∈ ((a.fam row col).t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 row col t Ch₀ A ι w c₀ hP hkb α
  have hr := hP.ram 0 (Nat.zero_le _)
  have hq := hP.rdq 0 (Nat.zero_le _)
  have hl := hP.live
  have hok : I.Ok := hW.tr.ok
  obtain ⟨hpins⟩ := hW.tr.pins
  obtain ⟨hstd⟩ := hW.tr.std
  obtain ⟨l0, -⟩ := hW.tw
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := ha2.pinX.inf
  refine ⟨fun φ => ⟨?_, fun y => ?_⟩, fun ψ hψ => ?_⟩
  · show _ ∈ (col t).Ram 0
    exact (hr _).2 ⟨(GlobalTheory.T.stepZero_ramifiedForms_transport_iff I hok l Z l0 u (W.P.I.tup t) _).1 ((I.rec7 l Z).eMu u φ).2, fun c hc => absurd (hl.first _) hc⟩
  · show (col t).rd 0 α _ y = _
    refine (hq α _ y).trans ?_
    exact GlobalTheory.T.scalarForm_transportedColumn_stepZero_standard I hok hpins l Z _ hstd u (W.P.I.tup t) Ch₀ A hP.is (ι 0 α) (hkb _) _ hθ _ ((I.rec7 l Z).eMu u φ).2 y
  · have h1 : GlobalTheory.AdForm.RamT 0 ψ := ((hr ψ).1 hψ).1
    have h2 : ((I.rec7 l Z).e0Tw u (W.P.I.tup t)).symm ψ ∈ ((I.rec7 l Z).mem u).A.Mram :=
      (GlobalTheory.T.stepZero_ramifiedForms_transport_iff I hok l Z l0 u (W.P.I.tup t) _).2 (by rwa [LinearEquiv.apply_symm_apply])
    obtain ⟨φ, hφ⟩ := EquivLike.surjective ((I.rec7 l Z).eMu u) ⟨_, h2⟩
    refine ⟨φ, ?_⟩
    show ψ = (I.rec7 l Z).e0Tw u (W.P.I.tup t) (((I.rec7 l Z).eMu u) φ).1
    rw [hφ]
    exact (LinearEquiv.apply_symm_apply _ ψ).symm
end GlobalTheory.Fam
end
