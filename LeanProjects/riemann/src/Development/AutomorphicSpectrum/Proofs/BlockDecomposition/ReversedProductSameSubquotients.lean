import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotientAltBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCosocleComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbedding
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenRev

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

set_option maxHeartbeats 2000000 in

theorem isSubquotient_prodIrr_rev : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k →
    ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type}
      [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible →
      IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  intro k _ _ _ _ hA hGK h N x hd hd' W _ _ σ _ hi hsq

  obtain ⟨hdy, ⟨E1⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun a => x (Fin.rev a)) hd'

  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK (fun a => Zc.dualCl (x (Fin.rev a))) hdy
  have ex : (fun a => Zc.dualCl ((fun a => Zc.dualCl (x (Fin.rev a))) (Fin.rev a))) = x := funext fun a => by
    simp only [Fin.rev_rev]
    exact GlobalTheory.T.dual_class_involutive hA (x a)
  obtain ⟨E3⟩ := GlobalTheory.CompanionTheory.LSocle.prodIrr_congr ex hd2 hd
  have h1 : IsSubquotient σ ((prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy).comp (Zc.Cos.thetaW k N)) :=
    isSubquotient_of_equiv hsq (E2.trans E3).symm
  have h2 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy) := by
    have := GlobalTheory.CompanionTheory.WordProd.RowCell.isSubquotient_pullback (Zc.Cos.thetaW k N) h1
    rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW] at this
  have hs : IsSmooth (σ.comp (Zc.Cos.thetaW k N)) := h2.isSmooth (isSmooth_prodIrr _ _)
  have hi' : Representation.IsIrreducible (σ.comp (Zc.Cos.thetaW k N)) :=
    GlobalTheory.CosocleComp.isIrreducible_comp (GlobalTheory.CompanionTheory.LSocle.thetaW_surjective N) hi
  have h3 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (contra (prodIrr (fun a => x (Fin.rev a)) hd')) :=
    isSubquotient_of_equiv h2 E1.symm
  have h4 := GlobalTheory.T.isSubquotient_contra_of_isSubquotient (GlobalTheory.SqIntUnit.compactOpen_basis k N) _ _ (isSmooth_contra _) h3
  obtain ⟨E4⟩ := GlobalTheory.T.double_contragredient_of_induced_product hA (fun a => x (Fin.rev a)) hd'
  obtain ⟨E5⟩ := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK σ hs hi'
  exact isSubquotient_of_equiv_left E5.symm (isSubquotient_of_equiv h4 E4)

end GlobalTheory.CompanionTheory.GenRev
