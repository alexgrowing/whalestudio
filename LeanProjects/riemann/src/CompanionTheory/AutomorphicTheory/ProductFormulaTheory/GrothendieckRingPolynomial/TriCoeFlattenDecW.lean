import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContragredientProductIrreducibleImports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccursStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordOccursOfSubquotientImports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlattenStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

section TriLemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tri_coe_decW (Δ : Segment k) : ((decW Δ : List (IrrGL k)) : Multiset (IrrGL k)) = Δ.ms := by
  have e := GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn Δ.term
  rw [decW, ← e, Multiset.coe_reverse, Segment.ms, Fin.univ_val_map]

theorem tri_coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL k)) : Multiset (IrrGL k)) = (L : Multiset (Segment k)).bind Segment.ms := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, tri_coe_decW, ← Multiset.cons_coe,
      Multiset.cons_bind]

theorem tri_msupp_of_inShW {𝔪 : Multiset (Segment k)} {w : List (IrrGL k)} (H : InShW 𝔪 w) :
    msupp 𝔪 = (w : Multiset (IrrGL k)) := by
  obtain ⟨L, rfl, hS⟩ := H
  rw [msupp, ← tri_coe_flatten_decW]
  exact (Multiset.coe_eq_coe.2 (GlobalTheory.T.perm_flatten_of_shuffle _ _ hS)).symm

theorem tri_msupp_wtW {h : ℕ} {Γ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Γ 𝔫) :
    msupp 𝔫 = (wtW Γ : Multiset (IrrGL k)) := by
  have e : wtW Γ = (((List.ofFn Γ).reverse).map decW).flatten := by
    rw [wtW, GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, List.map_ofFn]
    try rfl
  rw [e, tri_coe_flatten_decW, Multiset.coe_reverse, ← Fin.univ_val_map, H.1, msupp]

theorem tri_sqLen_map_toA (𝔪 : Multiset (Segment k)) : Comb.sqLen (𝔪.map toA) = sq 𝔪 := by
  rw [Comb.sqLen, Multiset.map_map]
  rfl

end TriLemmas

theorem tri (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Cls k) :
    Tri k := by
  intro 𝔪 𝔫 h x y hd hx hy hm
  obtain ⟨Δ, hΔ, hΔL⟩ := hx
  obtain ⟨h', x', hd', ⟨Γ, hΓ, -⟩, -⟩ := id hy
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have w1 : Wd y.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA c.soc c.jac 𝔫 y.rep hy h' Γ hΓ
  have hs : IsSubquotient y.rep (prodIrr x hd) := jhMult_ne_zero_iff.1 hm
  have w2 : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr x hd) hs _ w1
  have sh : InShW (Finset.univ.val.map Δ) (wtW Γ) :=
    GlobalTheory.T.segment_product_word_in_shuffle hA c.jac x hd Δ hΔL (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ) w2
  rw [hΔ.1] at sh
  refine ⟨(tri_msupp_of_inShW sh).trans (tri_msupp_wtW hΓ).symm, ?_⟩
  by_cases he : 𝔪 = 𝔫
  · exact Or.inl he
  right
  have hL := GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ
  have hne : 𝔪.map toA ≠ (((List.ofFn Γ).map toA : List _) : Multiset _) := by
    rw [hL]
    intro e
    exact he (Multiset.map_injective GlobalTheory.CompanionTheory.ZcWords.toA_injective e)
  have key := GlobalTheory.T.shuffle_weight_square_length_lt sNu GlobalTheory.CompanionTheory.ZcWords.sNu_injective GlobalTheory.CompanionTheory.ZcWords.sNu_aperiodic
    ((List.ofFn Γ).map toA) (𝔪.map toA) (GlobalTheory.CompanionTheory.ZcWords.aOrdered_of_isOrderedForm hΓ)
    (GlobalTheory.CompanionTheory.ZcWords.inSh_of_inShW sh) hne
  rw [hL, tri_sqLen_map_toA, tri_sqLen_map_toA] at key
  exact key

end CompanionTheory.Groth

end
