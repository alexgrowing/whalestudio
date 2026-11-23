import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

open Formalism.BasicNotions.TH

namespace GlobalTheory.HeightCounting.Up.StandardFrameAgreement

theorem stdFrame_iff {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) :
    R3.StdFrame hF P ↔ GlobalTheory.NJoin.StdFrame hF P := by
  have key : ∀ {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2),
      R3.swapCast h = principalLevelFrame.tensCastR h := by
    intro E _ _ F1 F2 h
    subst h
    rfl
  unfold R3.StdFrame GlobalTheory.NJoin.StdFrame principalLevelFrame.StdPsi
  rw [key hF]

set_option maxHeartbeats 1000000 in

theorem agree_of_layer : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, Nonempty (GlobalTheory.NJoin.Agree (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) c.a.all.gal.mt (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf).rep) := by
  intro _ hL
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c hNE _ _ hC Xd E labPi hb htup hg hf
  obtain ⟨m⟩ := hNE
  have ad := m.ad
  refine ⟨⟨t.r.Y.hF, ad.PV, fun j => (stdFrame_iff _ _).1 (ad.std j), fun j => (stdFrame_iff _ _).1 (t.r.Y.stdPsi.2 j),
    fun _ => 1, ?_, fun μ hμ j => (ad.eW μ hμ j).symm, ?_, ?_, fun σ => ?_⟩⟩
  · intro j h
    simp only [inv_one, one_mul, mul_one]
    exact ad.rat j h
  · intro μ hμ j h γ hγ he v
    have he' := he
    simp only [inv_one, one_mul, mul_one] at he'
    have key := ad.wt μ hμ j h γ hγ he' ((ad.eW μ hμ j).symm v)
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    refine Eq.trans ?_ key.symm
    exact congrArg _ (LinearEquiv.apply_symm_apply _ v).symm
  · intro μ hμ j x h
    refine (LinearEquiv.eq_symm_apply _).2 ?_
    refine (ad.read μ hμ j x h).trans ?_
    simp only [inv_one, one_mul]
    rfl
  · exact Formalism.L2.NG.IsoRep.refl _

end GlobalTheory.HeightCounting.Up.StandardFrameAgreement
