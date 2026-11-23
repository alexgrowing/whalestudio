import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDualStatement
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Symm.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem segDual_nu (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (s : ℂ) :
    Zc.segDual (Δ.nu s) = (Zc.segDual Δ).nu (-s) := by
  have hc : ∀ x : IrrGL k, x.IsCusp → (Zc.dualCl x).IsCusp := fun x hx => (GlobalTheory.T.dual_class_cuspidal hA x hx).1
  refine Segment.ext_first ?_ ?_
  · show (Zc.segDual (Δ.nu s)).first = (Zc.segDual Δ).first.nu (-s)
    rw [GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc]
    show (Zc.dualCl (Δ.first.nu s)).nu (1 - ((Δ.len : ℕ) : ℂ)) = _
    rw [GlobalTheory.T.dual_class_twist_neg hA, IrrGL.nu_nu, IrrGL.nu_nu]
    congr 1
    ring
  · show (Zc.segDual (Δ.nu s)).len = (Zc.segDual Δ).len
    rw [GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc, GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc]
    rfl

theorem segDual_segDual (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Zc.segDual (Zc.segDual Δ) = Δ := by
  have hc : ∀ x : IrrGL k, x.IsCusp → (Zc.dualCl x).IsCusp :=
    fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  apply GlobalTheory.SmGL.Segment.ext_first
  · rw [GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc,
      GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA,
      GlobalTheory.LocGL.IrrGL.nu_nu, neg_add_cancel, GlobalTheory.LocGL.IrrGL.nu_zero]
  · rw [GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc, GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc]

set_option maxHeartbeats 800000 in

theorem isLSeg_dualCl (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} {δ : IrrGL k} (hL : IsLSeg Δ δ.rep) :
    IsLSeg (Zc.segDual Δ) (Zc.dualCl δ).rep := by
  have gk : Zc.Cos.GKLocal k := by
    intro N V _ _ π hs hi
    exact GlobalTheory.GelfandKazhdan.equiv_contra k N V π (hA k N V π hs hi) hi
  have hc : ∀ x : IrrGL k, x.IsCusp → (Zc.dualCl x).IsCusp :=
    fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  obtain ⟨hd, cos⟩ := hL
  have hlen : Δ.len = (Zc.segDual Δ).len := (GlobalTheory.CompanionTheory.SegDualPrec.len_segDual hc Δ).symm
  obtain ⟨hd1, ⟨e1⟩⟩ := GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW hA gk Δ.term hd
  obtain ⟨hdQ, ⟨e2⟩⟩ := GlobalTheory.CompanionTheory.SegIncDual.exists_equiv_prodIrr_of_cast hlen
    (fun a => Zc.dualCl (Δ.term a.rev)) (Zc.segDual Δ).term (by
      intro a
      rw [GlobalTheory.CompanionTheory.SegIncDual.dualCl_term hA Δ hlen]
      show (Zc.segDual Δ).term (Fin.cast hlen a.rev).rev = _
      congr 1
      ext
      simp [Fin.val_rev]
      omega) hd1
  have c1 : IsCosocle δ.rep
      (MonoidHom.comp (MonoidHom.comp (prodIrr Δ.term hd) (Zc.Cos.thetaW k _)) (Zc.Cos.thetaW k _)) := by
    rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW]
    exact cos
  have c2 := GlobalTheory.CompanionTheory.LSocle.isCosocle_comp_thetaW c1
  obtain ⟨e3⟩ := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra gk _ δ.rep δ.snd.rep.smooth δ.snd.rep.irr
  have c3 : IsCosocle (contra δ.rep) (prodIrr (Zc.segDual Δ).term hdQ) :=
    GlobalTheory.LocGL.IsCosocle.of_equiv c2 e3 (e1.trans e2)
  have key : ∀ (hs : IsSmooth (contra δ.rep)) (hi : (contra δ.rep).IsIrreducible),
      IsLSeg (Zc.segDual Δ) (IrrGL.of (contra δ.rep) hs hi).rep := by
    intro hs hi
    obtain ⟨e4⟩ := GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep
      (⟨_, contra δ.rep, hs, hi⟩ : IrrRep (GL (Fin δ.fst) k))
    exact ⟨hdQ, GlobalTheory.LocGL.IsCosocle.of_equiv c3 e4.symm (Representation.Equiv.refl _)⟩
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  exact key _ _

end PositivityTheory.Gud.Symm.Pf

end
