import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.OrthSum

variable {K : Type} [Field K] [NumberField K]

theorem disjoint_of_orth (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : Disjoint F G := by
  rw [Submodule.disjoint_def]
  intro x hxF hxG
  by_contra hx
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent (𝓞 K) (fun _ : Unit => x) := linearIndependent_unique_iff.mpr hx
  have hpos := gramDet_pos E.metric σ hli
  have h0 := h σ x hxF x hxG
  rw [← FibreSpace.inner_equiv E.metric σ] at h0
  have h0' : inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ x) = 0 := h0
  have hz : GroundTheory.Heights₂.Heights.gramDet E.metric σ (fun _ : Unit => x) = 0 := by
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_unique, Matrix.gram_apply, h0', Complex.zero_re]
  linarith

theorem gramDet_sumElim (E : HermitianBundle.{0} K) (σ : K →+* ℂ) {a b : ℕ}
    {s : Fin a → E.carrier} {t : Fin b → E.carrier} (hs : LinearIndependent (𝓞 K) s)
    (ht : LinearIndependent (𝓞 K) t)
    (h : ∀ i j, inner ℂ (fibreVec E.metric σ (s i)) (fibreVec E.metric σ (t j)) = 0) :
    gramDet E.metric σ (Sum.elim s t) = gramDet E.metric σ s * gramDet E.metric σ t := by
  have hconj : ∀ i j, inner ℂ (fibreVec E.metric σ (t j)) (fibreVec E.metric σ (s i)) = 0 := by
    intro i j
    rw [← inner_conj_symm, h i j, map_zero]
  have hM : (Matrix.gram ℂ fun k => fibreVec E.metric σ (Sum.elim s t k)) =
      Matrix.fromBlocks (Matrix.gram ℂ fun i => fibreVec E.metric σ (s i)) 0 0
        (Matrix.gram ℂ fun j => fibreVec E.metric σ (t j)) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, h, hconj]
  have him : ∀ {n : ℕ} (v : Fin n → FibreSpace E.metric σ), (Matrix.gram ℂ v).det.im = 0 := by
    intro n v
    have hA : (Matrix.gram ℂ v).conjTranspose = Matrix.gram ℂ v := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.gram_apply]
      exact inner_conj_symm _ _
    have hdet := Matrix.det_conjTranspose (Matrix.gram ℂ v)
    rw [hA] at hdet
    exact Complex.conj_eq_iff_im.mp hdet.symm
  unfold GroundTheory.Heights₂.Heights.gramDet
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, him, him, mul_zero, sub_zero]

theorem degree_sup (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : E.degree (F ⊔ G) = E.degree F + E.degree G := by
  have hd : Disjoint F G := disjoint_of_orth E h
  obtain ⟨s, hs, hsF⟩ := CoverDenseAlt.exists_fam E F
  obtain ⟨t, ht, htG⟩ := CoverDenseAlt.exists_fam E G
  have hNs : Submodule.span (𝓞 K) (Set.range s) ≤ F := CoverDenseAlt.span_le_of_mem hsF
  have hNt : Submodule.span (𝓞 K) (Set.range t) ≤ G := CoverDenseAlt.span_le_of_mem htG
  have hst : LinearIndependent (𝓞 K) (Sum.elim s t) := hs.sum_type ht (hd.mono hNs hNt)
  have hmem : ∀ i, Sum.elim s t i ∈ F ⊔ G := by
    rintro (i | i)
    · exact Submodule.mem_sup_left (hsF i)
    · exact Submodule.mem_sup_right (htG i)
  have hcard : Fintype.card (Fin (E.rank F) ⊕ Fin (E.rank G)) = E.rank (F ⊔ G) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, CoverDenseAlt.rank_sup E hd]
  obtain ⟨hiF, hF⟩ := CoverDenseAlt.deg_eq E F hs hsF (Fintype.card_fin _)
  obtain ⟨hiG, hG⟩ := CoverDenseAlt.deg_eq E G ht htG (Fintype.card_fin _)
  obtain ⟨-, hFG⟩ := CoverDenseAlt.deg_eq E (F ⊔ G) hst hmem hcard
  have hidx : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Sum.elim s t))) (F ⊔ G) =
      CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range s)) F * CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range t)) G := by
    rw [Set.Sum.elim_range, Submodule.span_union,
      ← CoverDenseAlt.idx_mul (sup_le_sup_right hNs _) (sup_le_sup_left hNt F)]
    congr 1
    · exact CoverDenseAlt.idx_sup hNs (hd.mono_right hNt)
    · rw [sup_comm F, sup_comm F G]
      exact CoverDenseAlt.idx_sup hNt hd.symm
  have hlog : ∀ σ : K →+* ℂ, Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ (Sum.elim s t)) =
      Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ s) + Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ t) := by
    intro σ
    have hgram := gramDet_sumElim E σ hs ht (fun i j => by
      have h1 := h σ _ (hsF i) _ (htG j)
      rw [← FibreSpace.inner_equiv E.metric σ] at h1
      exact h1)
    rw [hgram, Real.log_mul (gramDet_pos E.metric σ hs).ne' (gramDet_pos E.metric σ ht).ne']
  rw [hFG, hF, hG, hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hiF) (Nat.cast_ne_zero.mpr hiG)]
  simp only [hlog, Finset.sum_add_distrib]
  ring

theorem degree_bot (E : HermitianBundle.{0} K) : E.degree ⊥ = 0 := by
  have hrk : Fintype.card (Fin 0) = E.rank ⊥ := by
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  obtain ⟨-, hdeg⟩ := CoverDenseAlt.deg_eq E ⊥ (s := (Fin.elim0 : Fin 0 → E.carrier)) linearIndependent_empty_type
    (fun i => i.elim0) hrk
  have h1 : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Fin.elim0 : Fin 0 → E.carrier))) ⊥ = 1 := by
    rw [CoverDenseAlt.idx_eq_card]
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨0⟩⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Subsingleton.elim a b]
  have hg : ∀ σ : K →+* ℂ, GroundTheory.Heights₂.Heights.gramDet E.metric σ (Fin.elim0 : Fin 0 → E.carrier) = 1 := by
    intro σ
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_isEmpty, Complex.one_re]
  rw [hdeg, h1]
  simp only [hg, Real.log_one, Nat.cast_one, Finset.sum_const_zero, mul_zero, sub_zero]

theorem orth_biSup (E : HermitianBundle.{0} K) {F : Submodule (𝓞 K) E.carrier} {I : Type}
    (G : I → Submodule (𝓞 K) E.carrier) (S : Finset I) (h : ∀ b ∈ S, OrthAt E F (G b)) :
    OrthAt E F (⨆ b ∈ S, G b) := by
  classical
  intro σ x hx y hy
  obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum G y).mp hy
  rw [← FibreSpace.inner_equiv E.metric σ]
  have hfv : fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier)) = ∑ b ∈ S, fibreVec E.metric σ (μ b) := by
    simpa using fibreVec_sum E.metric σ S (fun _ => 1) (fun b => (μ b : E.carrier))
  change inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier))) = 0
  rw [hfv, inner_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  have h1 := h b hb σ x hx _ (μ b).2
  rw [← FibreSpace.inner_equiv E.metric σ] at h1
  exact h1

theorem degree_rank_biSup (E : HermitianBundle.{0} K) {I : Type}
    (F : I → Submodule (𝓞 K) E.carrier) (h : ∀ a b, a ≠ b → OrthAt E (F a) (F b)) (S : Finset I) :
    E.degree (⨆ a ∈ S, F a) = ∑ a ∈ S, E.degree (F a) ∧
      E.rank (⨆ a ∈ S, F a) = ∑ a ∈ S, E.rank (F a) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · have hb : (⨆ a ∈ (∅ : Finset I), F a) = ⊥ := by simp
    rw [hb, Finset.sum_empty, Finset.sum_empty]
    refine ⟨degree_bot E, ?_⟩
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  · intro a S ha ih
    rw [Finset.iSup_insert, Finset.sum_insert ha, Finset.sum_insert ha]
    have horth : OrthAt E (F a) (⨆ b ∈ S, F b) :=
      orth_biSup E F S fun b hb => h a b fun hab => ha (hab ▸ hb)
    refine ⟨?_, ?_⟩
    · rw [degree_sup E horth, ih.1]
    · rw [CoverDenseAlt.rank_sup E (disjoint_of_orth E horth), ih.2]

theorem normDegree_rank_iSup : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  intro K _ _ E I _ F h
  have hU : (⨆ a, F a) = ⨆ a ∈ (Finset.univ : Finset I), F a := by simp
  obtain ⟨hd, hr⟩ := degree_rank_biSup E F h Finset.univ
  rw [hU]
  refine ⟨?_, hr⟩
  unfold GroundTheory.Heights₂.Heights.HermitianBundle.normDegree
  rw [hd, Finset.sum_div]

end GlobalTheory.CompanionTheory.Ar.OrthSum
