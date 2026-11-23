import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.PerId
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_crd_equiv (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ}
    {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) :
    ∃ e : Df.MtCx I a ≃ₗ[ℂ] s.A.T, ∀ y, IsCrd I hX a e
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y) := by
  obtain ⟨e, he⟩ := ColTie.exists_equiv_of_bases (σ := ColTie.sig X.B)
    (n := ColTie.dimP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX)
    (ColTie.jP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B)) t.j
    (ColTie.linearIndependent_jP_single (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    (ColTie.span_range_jP_single_eq_top (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    t.forms.li t.forms.span
  refine ⟨e, fun y => ⟨ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y, ?_, (he y).symm⟩⟩
  exact ⟨(ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y),
    ColTie.zOf_mem (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩

set_option maxHeartbeats 400000 in

theorem exists_perT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px)) (tA : ∀ a : w.I.ι, Tie1 (w.st Z).toD7.what₂.embLL (mAU (w.st Z) w.I hX Xg tr true a) (p.sA true a)), ∃ d : PerD p, Nonempty (PerT w Z hX Xg tr p (fun a x => (tA a).j x) d) := by
  intro B f T w Z hX Xg tr p tA
  have hE := fun a : w.I.ι => exists_crd_equiv (w.st Z) w.I hX Xg tr a (tA a)
  choose e he using hE
  have hG : ∀ u a, ∃ g : Df.MtCx w.I a ≃ₗ[ℂ] (TC.per w.I w.l u a).Mt, ∀ F, Df.SameForm w.I w.l u a F (g F) := fun u a =>
    Df.mtCx_equiv_per w.I w.ok w.pins w.l hX u a
  choose g hg using hG
  refine ⟨⟨fun u => (g u w.I.mu0).symm.trans (e w.I.mu0), fun u a => (g u a).symm.trans (e a)⟩, ⟨⟨e, ?_, ?_, he⟩⟩⟩
  · intro u F
    have h1 : ((g u w.I.mu0).symm.trans (e w.I.mu0)).symm (e w.I.mu0 F) = g u w.I.mu0 F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u w.I.mu0 F
  · intro u a F
    have h1 : ((g u a).symm.trans (e a)).symm (e a F) = g u a F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u a F

end GlobalTheory.Mem.R3.Rw.PerId
