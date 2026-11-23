import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FamAllQ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
def qPrime_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (p : ℕ) : Prop := ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
def FamilyRatioCondition {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) : Prop :=
  ∀ n, 2 * n = D.R.m → ∀ t, (f.t t).cTop n ≠ 0 ∧ UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) ((f.t t).cTop n / (f.t t).cBot)
    ((f.t W.P.A3.A.μ0).cTop n / (f.t W.P.A3.A.μ0).cBot)
def FamilyServedCondition (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  ∀ w (p : ℕ), p.Prime → _root_.GlobalTheory.MiTop.qPrime_alt W (W.Q.Rl.mu w) p → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal
def FamilyAllConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u),
    d.Pin z ∧ LawsX f.t ∧ _root_.GlobalTheory.MiTop.LinkVanishes f d ∧ _root_.GlobalTheory.MiTop.LinkTailCondition f ∧ _root_.GlobalTheory.MiTop.LinkDescends f ∧ _root_.GlobalTheory.MiTop.LinkSurjective f ∧ _root_.GlobalTheory.MiTop.LinkCommutes f ∧ _root_.GlobalTheory.MiTop.FamilyRatioCondition f
end GlobalTheory.MiTop
end
end
