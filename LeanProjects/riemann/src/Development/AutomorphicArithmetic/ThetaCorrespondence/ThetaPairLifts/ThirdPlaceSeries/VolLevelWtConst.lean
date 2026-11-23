import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsVolumeData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevMulWtMidStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenVolStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem vol_level_wt_const_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ (V : ℕ → ℂ) (VT : ℂ), (∀ j, j < B.R.m → V j ≠ 0) ∧ VT ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.Vol V ∧ J.VolT VT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT
  obtain ⟨VT, hVT, hT3⟩ := _root_.GlobalTheory.T.exists_volume_constant_of_true_geometry W hW u a ha haT
  refine ⟨fun j => if h : j + 2 ≤ B.R.m then Classical.choose (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)
    else if h' : j + 1 = B.R.m then Classical.choose (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h') else 1, VT, ?_, hVT, ?_⟩
  · intro j hj
    by_cases h : j + 2 ≤ B.R.m
    · simp only [dif_pos h]; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)).1
    · have h' : j + 1 = B.R.m := by omega
      simp only [dif_neg h, dif_pos h']; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h')).1
  · intro t J hJ
    refine ⟨?_, hT3 t J hJ⟩
    intro j hj α
    by_cases h : j + 2 ≤ B.R.m
    · simp only [dif_pos h]; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_identity_alt W hW u a ha haT j h)).2 t J hJ α
    · have h' : j + 1 = B.R.m := by omega
      simp only [dif_neg h, dif_pos h']; exact (Classical.choose_spec (_root_.GlobalTheory.T.true_geometry_chain_step_value_alt W hW u a ha haT j h')).2 t J hJ α
end GlobalTheory.Fam
end
