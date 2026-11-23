import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfSteps
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.NotAboveTransGenSelf
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtPOfFineUniq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrderedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGlStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.CsOrderfree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDualStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace PositivityTheory.Exh

variable (hZ : GlobalTheory.Published.SegmentRepresentation) (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZSeg.LUnlinkedIrr k)

include hZ hI in
theorem standardCosocle_of : GlobalTheory.Published.StandardCosocleGL := by
  have hA := irreducibleAdmissibleGL
  intro k _ _ _ _ _ 𝔪 h N x hd hx
  obtain ⟨Γ, hΓ, hL⟩ := GlobalTheory.T.langlands_factors_dual_reverse_ordered hA (GlobalTheory.T.langlands_segment_dual hA hZ) 𝔪 x hx
  obtain ⟨hd', ⟨e⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA x hd
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.reverse_ordered_product_has_socle hA (GlobalTheory.T.segment_jacquet_all hA hZ) (hI k) (GlobalTheory.T.unlinked_commute_of_irreducible k hA (hI k)) Γ (fun a => dualCl (x a)) hd' hΓ hL
  exact GlobalTheory.T.cosocle_of_contragredient_socle hA (prodIrr x hd) (isSmooth_prodIrr x hd) (GlobalTheory.T.product_irreducible_finite_length hA x hd) τ
    (hτ.of_equiv (Representation.Equiv.refl _) e.symm)

include hI in
theorem lOrderFree_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : LOrderFree k :=
  PositivityTheory.PfEss.Zc2.cs_orderfree irreducibleAdmissibleGL (GlobalTheory.T.unlinked_commute_of_irreducible k irreducibleAdmissibleGL (hI k))

include hI in
theorem lSocleGL_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : LSocleGL k :=
  GlobalTheory.T.langlands_socle_of_order_free irreducibleAdmissibleGL (GlobalTheory.T.local_langlands_of_irreducible_admissible irreducibleAdmissibleGL) (lOrderFree_of hI k)

include hZ hI in
theorem exhaustion_of_three (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], MidP k ∧ RefineP k ∧ SwapP k) : GlobalTheory.Published.LanglandsExhaustionGL := by
  have hA := irreducibleAdmissibleGL
  refine exhaustion_of_steps fun k _ _ _ _ _ => ?_
  obtain ⟨hM, hR, hS⟩ := H k
  have hC := cuspEmbP_of_refine k hR
  exact ⟨hM, hR, hS, hC, suppP k, juxtP_of_fineUniq hA hM hR hS hC (GlobalTheory.T.segment_product_word_in_shuffle hA (GlobalTheory.T.segment_jacquet_all hA hZ)) (GlobalTheory.T.irreducible_sub_segment_product hA hZ),
    linkP, minP, peelGoodP (standardCosocle_of hZ hI) (lSocleGL_of hI k) hR⟩

include hZ hI in
theorem multisegments_of (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments :=
  GlobalTheory.T.langlands_multisegments_of_exhaustion_gl irreducibleAdmissibleGL (lSocleGL_of hI) (fun _ _ _ _ _ => GlobalTheory.T.segment_jacquet_all irreducibleAdmissibleGL hZ) (lOrderFree_of hI) hE

end PositivityTheory.Exh

end
