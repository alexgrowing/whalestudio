import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepJacquetWordMultiplicityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProduct
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.ZWordL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_eq_decWord (Γ : Segment k) : decW Γ = Cos.decWord Γ := by
  apply List.ext_getElem
  · simp [decW, Cos.decWord]
  · intro n h1 h2
    simp only [decW, Cos.decWord, List.getElem_ofFn, List.getElem_reverse, List.length_ofFn, Fin.rev]
    congr 2
    omega

theorem isCusp_of_mem_decWord (Γ : Segment k) : ∀ w ∈ Cos.decWord Γ, w.IsCusp := by
  intro w hw
  simp only [Cos.decWord, List.mem_reverse, List.mem_ofFn] at hw
  obtain ⟨a, rfl⟩ := hw
  exact Γ.isCusp_term a

theorem sum_get_decWord (Γ : Segment k) : ∑ a, ((Cos.decWord Γ).get a).1 = Γ.deg := by
  have hc : ∀ a, ((Cos.decWord Γ).get a).1 = Γ.d := fun a => by
    have hm := List.get_mem (Cos.decWord Γ) a
    simp only [Cos.decWord, List.mem_reverse, List.mem_ofFn] at hm
    obtain ⟨i, hi⟩ := hm
    show ((List.ofFn Γ.term).reverse.get a).1 = Γ.d
    rw [← hi]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hc a), Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp [Cos.decWord, Segment.deg]

theorem nontrivial_of_isIrreducible {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (h : σ.IsIrreducible) : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  haveI : IsSimpleOrder (Subrepresentation σ) := h
  exact bot_ne_top (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _) :
    (⊥ : Subrepresentation σ) = ⊤)

theorem wd_wtW_of_isL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → ∀ (𝔪 : Multiset (Segment k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → ∀ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 → Wd π (wtW Δ) := by
  intro k _ _ _ _ hA hS hJ 𝔪 N V _ _ π hπ h Δ hΔ
  have hmem : ∀ i, Δ i ∈ 𝔪 := fun i => hΔ.1 ▸ Multiset.mem_map_of_mem Δ (Finset.mem_univ i)
  choose x hx using fun i => SumProd.exists_isLSeg_of_isL hπ (hmem i)
  have hF : LFactors 𝔪 x := ⟨Δ, hΔ, hx⟩
  have hd0 : ∑ a, (x a).1 = N := (SumProd.sum_fst_of_lFactors hF).trans (SumProd.deg_of_isL hπ)
  have hd : ∑ a, (x (Fin.rev a)).1 = N := (Equiv.sum_comp Fin.revPerm (fun a => (x a).1)).trans hd0
  obtain ⟨hirr, f, hfinj, -⟩ := hS 𝔪 h N x hd hF π hπ
  obtain ⟨h', x', hd', hF', hcos⟩ := hπ
  have hsm : IsSmooth π := IsSubquotient.isSmooth (IsCosocle.isSubquotient hcos) (isSmooth_prodIrr _ _)
  have hfl : HasFiniteLength π := hasFiniteLength_of_isIrreducible hirr
  haveI := nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 : 1 ≤ jm (x ∘ Fin.rev) hd π :=
    GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x ∘ Fin.rev) hd π hsm f
      ⟨v, fun h0 => hv (hfinj (h0.trans (map_zero f).symm))⟩
  have hW : ∀ b, ∑ a, ((Cos.decWord (Δ (Fin.rev b))).get a).1 = ((x ∘ Fin.rev) b).1 := fun b =>
    (sum_get_decWord _).trans (hx (Fin.rev b)).deg_eq
  have h2 := GlobalTheory.T.jacquet_multiplicity_transitive_le hA (x ∘ Fin.rev) hd (fun b => Cos.decWord (Δ (Fin.rev b))) π hsm hfl hW
  have h3 : ∀ b, Cos.jmL (Cos.decWord (Δ (Fin.rev b))) ((x ∘ Fin.rev) b).rep = 1 := fun b =>
    (GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Δ (Fin.rev b)) _ (hx (Fin.rev b)) _ (isCusp_of_mem_decWord _)).1 rfl
  rw [Finset.prod_congr rfl (fun b _ => h3 b), Finset.prod_const_one, mul_one] at h2
  have h4 := h1.trans h2
  have hw : (List.ofFn fun b => Cos.decWord (Δ (Fin.rev b))).flatten = wtW Δ := by
    simp only [wtW, decW_eq_decWord]
  rw [hw] at h4
  unfold Cos.jmL at h4
  split_ifs at h4 with hdw
  · exact ⟨hdw, fun h0 => by rw [h0] at h4; simp at h4⟩
  · simp at h4

end GlobalTheory.CompanionTheory.ZWordL
