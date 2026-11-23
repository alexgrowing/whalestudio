import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccursStatement

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Multisegment

theorem inShW_of_wd_cosocle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSeg : LSegJacquet k)
    {𝔫 : Multiset (Segment k)} {N h h' : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (Δ : Fin h → Segment k) (Γ : Fin h' → Segment k)
    (v : Fin h' → IrrGL k) (hd : ∑ a, (v a).1 = N) (hΓ : IsOrderedForm Γ 𝔫)
    (hv : ∀ i, IsLSeg (Γ i) (v i).rep) (hc : IsCosocle π (prodIrr v hd)) (hw : Wd π (wtW Δ)) :
    InShW 𝔫 (wtW Δ) := by
  have h1 : Wd (prodIrr v hd) (wtW Δ) :=
    GlobalTheory.T.word_occurs_of_subquotient (prodIrr v hd) π (isSmooth_prodIrr v hd) hc.isSubquotient _ hw
  have h2 := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg v hd Γ hv (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ) h1
  rwa [hΓ.1] at h2

theorem lInjective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k) (hSeg : LSegJacquet k) : LInjective k := by
  intro 𝔪 𝔫 x h𝔪 h𝔫
  obtain ⟨h, u, hd, ⟨Δ, hΔ, hu⟩, hc⟩ := id h𝔪
  obtain ⟨h', v, hd', ⟨Γ, hΓ, hv⟩, hc'⟩ := id h𝔫
  have wΔ : Wd x.rep (wtW Δ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 x.rep h𝔪 h Δ hΔ
  have wΓ : Wd x.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 x.rep h𝔫 h' Γ hΓ
  exact GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA 𝔪 𝔫 h h' Δ Γ hΔ hΓ
    (inShW_of_wd_cosocle hA hSeg Δ Γ v hd' hΓ hv hc' wΔ)
    (inShW_of_wd_cosocle hA hSeg Γ Δ u hd hΔ hu hc wΓ)

end GlobalTheory.CompanionTheory.Multisegment
