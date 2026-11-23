import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AdmissibilityClosed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefiniteRealisationChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinXRowOfGap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleOfTransported
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Top4 Formalism.L2.SG.JoinSI Formalism.L2.SG.PackageTie2
namespace Formalism.L2.SG.JoinSISel
section At
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
def IndefiniteRealisationMultiplicityCondition {R : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) : Prop :=
  (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).MIstar2 (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE
end At
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel} {selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK}
theorem complementFive_closed_of_image_v0 (selJ : _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationSelection 𝒜 sel selS selP selDH selC selK selI)
    (hM : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x hx h i => _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationMultiplicityCondition (selI Fm hc x hx h i))
    (hFX : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x hx h i => FinX (selS Fm hc x hx h i).Y)
    (hon : Closed 𝒜 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, BaseVectorImageFull (Fm.D x i)) :
    Closed 𝒜 fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  obtain ⟨ε1, hε1, H⟩ := (hM.and hFX).and hon
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨hM', hF'⟩, ⟨y0, hY⟩⟩ := hK Fm CH hc hL
  obtain ⟨a0, hA⟩ := hM' hc
  obtain ⟨b0, hB⟩ := hF' hc
  refine ⟨max (max a0 b0) (max y0 (max (sel Fm hc).1 (Fm.x1 + 1))), fun x hxge i => ?_⟩
  have h1 : max a0 b0 ≤ x := le_trans (le_max_left _ _) hxge
  have h2 : max y0 (max (sel Fm hc).1 (Fm.x1 + 1)) ≤ x := le_trans (le_max_right _ _) hxge
  have hx : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)
    linarith
  have h : (sel Fm hc).1 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h2)
  exact _root_.Formalism.L2.SG.JoinSI.adm13_of_kernel_join (hA x hx h (le_trans (le_max_left _ _) h1) i) (selJ Fm hc x hx h i)
    (hB x hx h (le_trans (le_max_right _ _) h1) i) (hY x (le_trans (le_max_left _ _) h2) i)
end Formalism.L2.SG.JoinSISel
end
