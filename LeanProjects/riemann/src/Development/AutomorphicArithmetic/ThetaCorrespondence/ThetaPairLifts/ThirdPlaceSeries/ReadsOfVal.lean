import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamCol
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}
variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}
variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def ValEqvAlt (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) : Prop :=
  ∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
    GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = (_root_.GlobalTheory.Fam.pk_z W).cX.ρ γ.1 (c v)
def packageAtPoint (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : (_root_.GlobalTheory.Fam.pk_z W).cX.W :=
  ((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h)
def PackageValuation (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) : Prop :=
  ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
    ∀ h y, HasMat h y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x h = c (val φ (latOf I (W.P.I.tup t) y))
def ValuationCompatible (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) : Prop :=
  ∀ w v, (_root_.GlobalTheory.Fam.pk_z W).prX (c w) v = pairVal B (j v) w
end GlobalTheory.TopVal
end
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}
variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
set_option maxHeartbeats 1000000 in
theorem reads_of_pairVal (hC : I.StdC l Z W.R.T.cols) (hW : _root_.GlobalTheory.AdForm.TwStdAlt W) (u : B.Word)
    (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) (a : (I.rec7 l Z).what₂.Tup) (φ : Frm I a)
    (G : (I.rec7 l Z).what₂.Amb a) (hG : RecVal u a φ G)
    (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → ℂ))
    (hf : ∀ h y (p : XPt (B.primes X) B.R I.sel (I.tup a)) v, HasMat h y → TC.PtOf y p →
      f v h = pairVal B (j v) (val φ (toRow I.sel (I.tup a) p))) :
    _root_.GlobalTheory.Fam.ReadsCoefficients W u j 1 a G f := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    intro c v g hg
    have s := hC u
    rw [mul_one, hf g _ _ v hg (s.what₂.pt c)]
    have e := fun c' y => (s.eW ((W.R.T.cols.forms u).valP.eW.symm (Pi.single c (j v))) c' y y rfl).symm
    simp only [LinearEquiv.apply_symm_apply] at e
    refine (period_single l u I.mu0 φ _ (hG.1 rfl) c (j v) _ (funext fun y => (e c y).trans ?_)
      fun c' hc => funext fun y => (e c' y).trans ?_).symm
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
      rfl
  · obtain ⟨l0, t, he, ht, -, -, s⟩ := hW
    have key : ∀ (Tw : TwForms (I.rec7 l Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols Tw), Tw = I.tw l l0 Z → HEq t' t →
        ReadsG (t'.pt.cls u a h) (t'.pt.val u a h).eW j 1 (((I.rec7 l Z).eMtTw u a).symm G) f := by
      rintro _ t' rfl rfl
      intro c v g hg
      rw [mul_one, hf g _ _ v hg ((s.what₂ u a h).pt c)]
      have e := fun c' y => (s.eW u a h ((t'.pt.val u a h).eW.symm (Pi.single c (j v))) c' y y rfl).symm
      simp only [LinearEquiv.apply_symm_apply] at e
      refine (period_single l u a φ _ hG.2 c (j v) _ (funext fun y => (e c y).trans ?_)
        fun c' hc => funext fun y => (e c' y).trans ?_).symm
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
        rfl
    exact key _ _ he ht
end GlobalTheory.TopVal
end
end
