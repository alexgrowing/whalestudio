import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountableFractionRingMvPolynomial
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

noncomputable section

namespace GlobalTheory.FlatLine

open IntermediateField in

theorem mem_range_of_embeddings_const {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Countable Ω] [Algebra K Ω]
    [Algebra K ℂ] (P₀ : Ω →ₐ[K] ℂ) {b : Ω} {a : ℂ} (h : ∀ P : Ω →ₐ[K] ℂ, P b = a) :
    a ∈ (algebraMap K ℂ).range := by
  have hb : IsIntegral K b :=
    (isAlgebraic_of_norm_const P₀ fun P => by rw [h P, h P₀]).isIntegral
  haveI : FiniteDimensional K K⟮b⟯ := adjoin.finiteDimensional hb
  have key : ∀ ψ : K⟮b⟯ →ₐ[K] ℂ, ψ (AdjoinSimple.gen K b) = a := fun ψ => by
    letI : Algebra K⟮b⟯ ℂ := ψ.toRingHom.toAlgebra
    obtain ⟨Q⟩ := GlobalTheory.nonempty_algHom_complex_of_countable K⟮b⟯ Ω
    let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
      commutes' := fun k => (Q.commutes (algebraMap K K⟮b⟯ k)).trans (ψ.commutes k) }
    rw [← h P]
    exact (Q.commutes (AdjoinSimple.gen K b)).symm
  have hsub : Subsingleton (K⟮b⟯ →ₐ[K] ℂ) := ⟨fun ψ χ =>
    (adjoin.powerBasis hb).algHom_ext (by rw [adjoin.powerBasis_gen, key, key])⟩
  have h1 : Module.finrank K K⟮b⟯ = 1 := by
    have h2 := AlgHom.card K K⟮b⟯ ℂ
    have h3 : Fintype.card (K⟮b⟯ →ₐ[K] ℂ) ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 hsub
    have h4 : 0 < Module.finrank K K⟮b⟯ := Module.finrank_pos
    omega
  obtain ⟨k, hk⟩ := mem_bot.1 (finrank_adjoin_simple_eq_one_iff.1 h1)
  exact ⟨k, by rw [← h P₀, ← hk, P₀.commutes]⟩

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt

theorem const_value_mem_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q →
    ∀ f ∈ sec Xo c 0 0, ∀ a : ℂ, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = a) → a ∈ σ.range := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 g hg a ha
  obtain ⟨hL, -, h, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨Z⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l Xo c h1).1
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, toC (P (evC h Z g)) = a := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (one_mul _).trans (ha k x x.2)
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  haveI hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)
  have hO : Countable (Om Z) := GlobalTheory.GenericReading.countable_fractionRing_mvPolynomial _ _
  letI : Algebra c.F ℂ := σ.toAlgebra
  exact mem_range_of_embeddings_const (K := c.F) (b := evC h Z g) P₀ key

end GlobalTheory.FlatLine
