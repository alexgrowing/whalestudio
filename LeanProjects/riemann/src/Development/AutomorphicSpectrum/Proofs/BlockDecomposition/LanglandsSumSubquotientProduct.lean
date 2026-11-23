import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NonemptyEquivParIndZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegmentsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsClassificationOrderFreeEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleaveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccursStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LangSumSub

theorem isL_of_exhaust {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hEx : ∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) {N : ℕ} (τ : IrrRep (GL (Fin N) k)) :
    ∃ 𝔭 : Multiset (Segment k), IsL 𝔭 τ.ρ := by
  obtain ⟨𝔭, h𝔭⟩ := hEx (IrrGL.of τ.ρ τ.smooth τ.irr)
  exact ⟨𝔭, h𝔭.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irr).symm⟩

set_option maxHeartbeats 1000000 in

theorem isSubquotient_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k)
    (hSeg : LSegJacquet k) (hFree : LOrderFree k) (hEx : ∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep)
    (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1)
    (h0 : IsL 𝔪 (x 0).rep) (h1 : IsL 𝔫 (x 1).rep) (hy : IsL (𝔪 + 𝔫) y.rep) : IsSubquotient y.rep (prodIrr x hd) := by
  obtain ⟨n, c⟩ := y
  obtain rfl : (x 0).1 + (x 1).1 = n := (Fin.sum_univ_two _).symm.trans hd
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr_rep x hd
  have hPs : IsSmooth (prodIrr x hd) := isSmooth_prodIrr x hd
  have hPf := GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  obtain ⟨h₁, h₂, h, Δ₁, Δ₂, Δ, hΔ₁, hΔ₂, hΔ, hI⟩ := GlobalTheory.T.ordered_forms_interleave_sum hA 𝔪 𝔫
  have w0 : Wd (x 0).rep (wtW Δ₁) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 (x 0).rep h0 h₁ Δ₁ hΔ₁
  have w1 : Wd (x 1).rep (wtW Δ₂) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 (x 1).rep h1 h₂ Δ₂ hΔ₂
  have wp : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Δ) :=
    GlobalTheory.T.word_occurs_product_interleave hA (x 0) (x 1) _ _ _ (GlobalTheory.T.ordered_word_letters_cuspidal Δ₁) (GlobalTheory.T.ordered_word_letters_cuspidal Δ₂) w0 w1 hI
  have wP : Wd (prodIrr x hd) (wtW Δ) := GlobalTheory.T.word_occurs_of_subquotient (prodIrr x hd) (prod₂ (x 0).rep (x 1).rep) hPs
    (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) _ wp
  have hτ := GlobalTheory.T.word_occurs_irreducible_subquotient hA (prodIrr x hd) hPs hPf (wtW Δ) wP
  obtain ⟨τ, hτP, hτW⟩ := hτ
  obtain ⟨𝔭, hτL⟩ := isL_of_exhaust hEx τ
  obtain ⟨h', z, hz, ⟨Γ, hΓ, hzL⟩, hcos⟩ := id hτL
  have s1 : InShW 𝔭 (wtW Δ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z hz Γ hzL (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z hz) hcos.isSubquotient _ hτW)
    rwa [hΓ.1] at this
  have wΓ : Wd τ.ρ (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔭 τ.ρ hτL h' Γ hΓ
  have wΓP : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ hPs hτP _ wΓ
  have wΓ2 : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prod₂ _ _)
    (.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective) _ wΓP
  obtain ⟨h'', z', Δ', hz', hz'L, hmap, hsub⟩ := GlobalTheory.T.product_langlands_subquotient_segments hA 𝔪 𝔫 (x 0) (x 1) h0 h1
  have s2 : InShW (𝔪 + 𝔫) (wtW Γ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z' hz' Δ' hz'L (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z' hz') hsub _ wΓ2)
    rwa [hmap] at this
  have he : 𝔪 + 𝔫 = 𝔭 := GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA (𝔪 + 𝔫) 𝔭 h h' Δ Γ hΔ hΓ s1 s2
  obtain ⟨ψ⟩ := GlobalTheory.T.langlands_classification_order_free_equiv hFree (𝔪 + 𝔫) τ.ρ (IrrGL.rep ⟨_, c⟩) (he ▸ hτL) hy
  exact (IsSubquotient.of_surjective ψ.toIntertwiningMap ψ.toLinearEquiv.surjective).trans hτP

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k →
    (∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) →
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) :=
  fun hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy =>
    isSubquotient_prodIrr hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy

end GlobalTheory.CompanionTheory.LangSumSub

end
