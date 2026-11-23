import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CocycleZeroMemInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

theorem HermDatum.exists_emb_or_conj (A : HermDatum Em Ψ N j) (σ : Em →+* ℂ) :
    ∃ τ, A.emb τ = σ ∨ (starRingEnd ℂ).comp (A.emb τ) = σ := by
  by_cases h : ∃ τ, A.emb τ = σ
  · obtain ⟨τ, hτ⟩ := h
    exact ⟨τ, Or.inl hτ⟩
  · have h' : ∃ τ, A.emb τ = (starRingEnd ℂ).comp σ := by
      by_contra h''
      exact h ((A.cmType σ).2 h'')
    obtain ⟨τ, hτ⟩ := h'
    refine ⟨τ, Or.inr ?_⟩
    rw [hτ]
    ext x
    simp

theorem HermDatum.finrank_eq (A : HermDatum Em Ψ N j) : Module.finrank ℚ Em = 2 * Fintype.card Ψ := by
  classical
  let g : Ψ ⊕ Ψ → (Em →+* ℂ) := Sum.elim A.emb fun τ => (starRingEnd ℂ).comp (A.emb τ)
  have hconj : ∀ τ τ', A.emb τ ≠ (starRingEnd ℂ).comp (A.emb τ') := by
    intro τ τ' h
    have h1 := (A.cmType (A.emb τ')).1 ⟨τ', rfl⟩
    refine h1 ⟨τ, ?_⟩
    rw [h]
  have hg : Function.Bijective g := by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (A.emb_inj h)
      · exact absurd h (hconj a b)
      · exact absurd h.symm (hconj b a)
      · refine congrArg Sum.inr (A.emb_inj (RingHom.ext fun x => ?_))
        have := congrArg (fun φ : Em →+* ℂ => starRingEnd ℂ (φ x)) h
        simpa [g] using this
    · intro σ
      obtain ⟨τ, h | h⟩ := A.exists_emb_or_conj σ
      exacts [⟨Sum.inl τ, h⟩, ⟨Sum.inr τ, h⟩]
  rw [← NumberField.Embeddings.card Em ℂ, ← Fintype.card_of_bijective hg, Fintype.card_sum]
  ring

theorem HermDatum.linearIndependent_real (A : HermDatum Em Ψ N j) {m : ℕ} {x : Fin m → Fin N → Em}
    (hx : LinearIndependent ℚ x) :
    LinearIndependent ℝ fun k (p : Ψ × Fin N) => A.emb p.1 (x k p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : ∀ τ a, ∑ k, (c k : ℂ) * A.emb τ (x k a) = 0 := by
    intro τ a
    have := congr_fun hc (τ, a)
    simpa [Finset.sum_apply, Complex.real_smul] using this
  have h2 : ∀ (σ : Em →+* ℂ) a, ∑ k, (c k : ℂ) * σ (x k a) = 0 := by
    intro σ a
    obtain ⟨τ, h | h⟩ := A.exists_emb_or_conj σ
    · rw [← h]
      exact h1 τ a
    · rw [← h]
      have := congrArg (starRingEnd ℂ) (h1 τ a)
      simpa [map_sum, Complex.conj_ofReal] using this
  set ω := NumberField.integralBasis Em
  have hxω : ∀ (σ : Em →+* ℂ) (y : Em), σ y = ∑ i, ((ω.repr y i : ℚ) : ℂ) * σ (ω i) := by
    intro σ y
    conv_lhs => rw [← ω.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
  have h3 : ∀ a i, ∑ k, c k * (ω.repr (x k a) i : ℝ) = 0 := by
    intro a
    have key : ∀ (σ : Em →+* ℂ),
        ∑ i, ((∑ k, c k * (ω.repr (x k a) i : ℝ) : ℝ) : ℂ) * σ (ω i) = 0 := by
      intro σ
      rw [← h2 σ a]
      simp only [hxω σ (x _ a)]
      push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    have hli := (NumberField.mixedEmbedding.latticeBasis Em).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    refine hli _ (Prod.ext (funext fun w => ?_) (funext fun w => ?_))
    · simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply,
        NumberField.mixedEmbedding.latticeBasis_apply,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul, Prod.fst_zero,
        Pi.zero_apply]
      apply Complex.ofReal_injective
      push_cast
      simp only [InfinitePlace.embedding_of_isReal_apply]
      have hk := key w.1.embedding
      push_cast at hk
      exact hk
    · simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
        NumberField.mixedEmbedding.latticeBasis_apply,
        NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex, Complex.real_smul,
        Prod.snd_zero, Pi.zero_apply]
      exact key _
  intro k
  rw [← Module.forall_dual_apply_eq_zero_iff ℚ (c k)]
  intro φ
  have h4 : ∑ k, φ (c k) • x k = 0 := by
    funext a
    apply ω.repr.injective
    ext i
    have := congrArg φ (h3 a i)
    rw [map_sum, map_zero] at this
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (c k), ← Rat.smul_def, map_smul, smul_eq_mul, mul_comm]
  exact Fintype.linearIndependent_iff.1 hx _ h4 k

theorem HermDatum.exists_isZBasis (A : HermDatum Em Ψ N j) {I : Submodule (𝓞 Em) (Fin N → Em)}
    (hI : I ≤ A.L) : ∃ m, ∃ b : Fin m → Fin N → Em, IsZBasis I b := by
  classical
  have hL : IsNoetherian ℤ (A.L.restrictScalars ℤ) := isNoetherian_of_fg_of_noetherian _ A.fg
  have hJ : IsNoetherian ℤ (I.restrictScalars ℤ) :=
    isNoetherian_of_le (s := I.restrictScalars ℤ) (t := A.L.restrictScalars ℤ) hI
  have hfin : Module.Finite ℤ (I.restrictScalars ℤ) := inferInstance
  have htf : Module.IsTorsionFree ℤ (I.restrictScalars ℤ) := inferInstance
  have hfree : Module.Free ℤ (I.restrictScalars ℤ) := Module.free_of_finite_type_torsion_free'
  let B := Module.finBasis ℤ (I.restrictScalars ℤ)
  have hspan : Submodule.span ℤ (Set.range fun k => (B k : Fin N → Em)) = I.restrictScalars ℤ := by
    have e : (Set.range fun k => (B k : Fin N → Em)) = (I.restrictScalars ℤ).subtype '' Set.range B :=
      Set.range_comp _ _
    rw [e, Submodule.span_image, B.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent ℤ ((I.restrictScalars ℤ).subtype ∘ B) :=
    B.linearIndependent.map' (I.restrictScalars ℤ).subtype (Submodule.ker_subtype _)
  refine ⟨_, fun k => (B k : Fin N → Em), hli, fun v => ?_⟩
  rw [hspan]
  rfl

omit [IsCMField Em] in

theorem card_eq_of_isZBasis {I : Submodule (𝓞 Em) (Fin N → Em)} {ρ : ℕ} {v : Fin ρ → Fin N → Em}
    (hv : IsNzFamily I ρ v) {m : ℕ} {b : Fin m → Fin N → Em} (hb : IsZBasis I b) :
    m = Module.finrank ℚ Em * ρ := by
  classical
  set ω := NumberField.integralBasis Em
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  have hvE : LinearIndependent Em v := (LinearIndependent.iff_fractionRing (𝓞 Em) Em).1 hv.2.2.1
  set w : _ × Fin ρ → Fin N → Em := fun p => ω p.1 • v p.2
  have hw : LinearIndependent ℚ w := linearIndependent_smul ω.linearIndependent hvE
  have hspan : Submodule.span ℚ (Set.range b) = Submodule.span ℚ (Set.range w) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hbk : b k ∈ I := (hb.2 _).2 (Submodule.subset_span ⟨k, rfl⟩)
      set T := Submodule.span (𝓞 Em) (Set.range v)
      have hmem : T.toAddSubgroup.relIndex I.toAddSubgroup • b k ∈ T.toAddSubgroup :=
        AddSubgroup.nsmul_relIndex_mem _ hbk
      have hT : ∀ t ∈ T, t ∈ Submodule.span ℚ (Set.range w) := by
        intro t ht
        obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).1 ht
        refine Submodule.sum_mem _ fun k _ => ?_
        rw [← algebraMap_smul Em (a k) (v k), ← ω.sum_repr (algebraMap (𝓞 Em) Em (a k)),
          Finset.sum_smul]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [smul_assoc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k), rfl⟩)
      have hn : (T.toAddSubgroup.relIndex I.toAddSubgroup : ℚ) ≠ 0 := by exact_mod_cast hv.2.2.2
      have := Submodule.smul_mem _ ((T.toAddSubgroup.relIndex I.toAddSubgroup : ℚ)⁻¹) (hT _ hmem)
      rwa [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn, one_smul] at this
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      have hpI : w p ∈ I := by
        show ω p.1 • v p.2 ∈ I
        rw [integralBasis_apply, algebraMap_smul]
        exact I.smul_mem _ (hv.2.1 p.2)
      exact Submodule.span_le_restrictScalars ℤ ℚ _ ((hb.2 _).1 hpI)
  have h1 := finrank_span_eq_card hbQ
  have h2 := finrank_span_eq_card hw
  rw [hspan, h2, Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_basis ω] at h1
  simpa using h1.symm

end GroundTheory.Heights₂.Heights.NineStatements
