import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem symm_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {σ : ℂ ≃+* ℂ} {τ τ₀ : E →+* ℂ}
    (hσ : ∀ y, σ (τ y) = τ₀ y) :
    (σ.symm : ℂ →+* ℂ).comp τ₀ = τ ∧
      (σ.symm : ℂ →+* ℂ).comp (ComplexEmbedding.conjugate τ₀) = ComplexEmbedding.conjugate τ := by
  constructor
  · refine RingHom.ext fun y => ?_
    simp [← hσ y]
  · refine RingHom.ext fun y => ?_
    have h1 : ComplexEmbedding.conjugate τ₀ y = τ₀ (IsCMField.complexConj E y) := by
      rw [ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
    have h2 : ComplexEmbedding.conjugate τ y = τ (IsCMField.complexConj E y) := by
      rw [ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
    rw [h2]
    simp [h1, ← hσ]

private theorem sum_reindex {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {σ : ℂ ≃+* ℂ} {τ τ₀ : E →+* ℂ} {x : E}
    (lam : (E →+* ℂ) → Fin n → ℕ) (hσ : ∀ y, σ (τ y) = τ₀ y) {ε : (E →+* ℂ) → ℕ}
    (hε : ∀ φ : E →+* ℂ, ε ((σ : ℂ →+* ℂ).comp φ) = if φ x = -τ x then 1 else 0) :
    ∑ φ ∈ (Finset.univ.erase τ₀).erase (ComplexEmbedding.conjugate τ₀), ε φ * ∑ j, UpperTheory.Gal.LocalSmoothExtension.conjWt σ lam φ j =
      ∑ φ ∈ (Finset.univ.erase τ).erase (ComplexEmbedding.conjugate τ), (if φ x = -τ x then 1 else 0) * ∑ j, lam φ j := by
  obtain ⟨e1, e2⟩ := symm_comp hσ
  have hA : ∀ φ : E →+* ℂ, (σ : ℂ →+* ℂ).comp ((σ.symm : ℂ →+* ℂ).comp φ) = φ := fun φ =>
    RingHom.ext fun y => by simp
  have hB : ∀ φ : E →+* ℂ, (σ.symm : ℂ →+* ℂ).comp ((σ : ℂ →+* ℂ).comp φ) = φ := fun φ =>
    RingHom.ext fun y => by simp
  refine Finset.sum_nbij' (fun φ => (σ.symm : ℂ →+* ℂ).comp φ) (fun φ => (σ : ℂ →+* ℂ).comp φ) ?_ ?_
    (fun φ _ => hA φ) (fun φ _ => hB φ) ?_
  · intro φ hφ
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hφ ⊢
    exact ⟨fun h => hφ.1 ((hA φ).symm.trans (by rw [h, ← e2, hA])),
      fun h => hφ.2 ((hA φ).symm.trans (by rw [h, ← e1, hA]))⟩
  · intro φ hφ
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hφ ⊢
    exact ⟨fun h => hφ.1 ((hB φ).symm.trans (by rw [h, e2])),
      fun h => hφ.2 ((hB φ).symm.trans (by rw [h, e1]))⟩
  · intro φ _
    have h := hε ((σ.symm : ℂ →+* ℂ).comp φ)
    rw [hA] at h
    rw [h]
    rfl

theorem UpperTheory.Gal.CertificateRingHomMap.pExpCore_of :
    UpperTheory.Gal.CertificateRingHomMap.ExpSum → UpperTheory.Gal.CertificateRingHomMap.ExpCore := by
  intro hS E _ _ _ n d x hd hx W m hm
  refine ⟨fun τ a b hab => ?_, fun τ τ₀ σ hσ ε hε k => ?_⟩
  · unfold lamOf
    split_ifs
    · exact le_rfl
    · exact Int.toNat_le_toNat (add_le_add_left ((W _).anti hab) _)
  · obtain ⟨e1, e2⟩ := symm_comp hσ
    have hs := hS E n d x hd hx W m hm τ
    rw [← sum_reindex (lamOf W m) hσ hε] at hs
    have c1 : ∀ i, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) τ₀ i = lamOf W m τ i := fun i => by
      show lamOf W m ((σ.symm : ℂ →+* ℂ).comp τ₀) i = _
      rw [e1]
    have c2 : ∀ i, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) (ComplexEmbedding.conjugate τ₀) i =
        lamOf W m (ComplexEmbedding.conjugate τ) i := fun i => by
      show lamOf W m ((σ.symm : ℂ →+* ℂ).comp (ComplexEmbedding.conjugate τ₀)) i = _
      rw [e2]
    generalize hR : (∑ φ ∈ (Finset.univ.erase τ₀).erase (ComplexEmbedding.conjugate τ₀),
      ε φ * ∑ j, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) φ j) = R at hs
    have hk : 0 < n := lt_of_le_of_lt (Nat.zero_le _) k.isLt
    rcases InfinitePlace.embedding_mk_eq τ with hv | hv
    · have hc : ComplexEmbedding.conjugate τ ≠ (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding := by
        rw [InfinitePlace.mk_conjugate_eq, hv]; exact conjugate_ne τ
      have l1 : ∀ i, lamOf W m τ i = m (InfinitePlace.mk τ) := fun i => if_pos hv.symm
      have l2 : ∀ i, ((lamOf W m (ComplexEmbedding.conjugate τ) i : ℕ) : ℤ) =
          (W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m (ComplexEmbedding.conjugate τ) i =
          ((W (InfinitePlace.mk (ComplexEmbedding.conjugate τ))).w i +
            m (InfinitePlace.mk (ComplexEmbedding.conjugate τ))).toNat := if_neg hc
        rw [h, InfinitePlace.mk_conjugate_eq]
        exact Int.toNat_of_nonneg (hm _ _)
      have hw : W.at τ = W (InfinitePlace.mk τ) := by
        have h := W.at_embedding (InfinitePlace.mk τ)
        rwa [hv] at h
      refine ⟨fun i => (m (InfinitePlace.mk τ) + R) +
        (∑ j ∈ Finset.univ.erase i, lamOf W m (ComplexEmbedding.conjugate τ) j + (i : ℕ)), k,
        Or.inr ⟨m (InfinitePlace.mk τ), fun i => by rw [c1, l1], fun i => ?_⟩, ?_⟩
      · simp only [c2, hR]
      · have hsum : ((∑ j ∈ Finset.univ.erase k, lamOf W m (ComplexEmbedding.conjugate τ) j : ℕ) : ℤ) =
            ∑ j ∈ Finset.univ.erase k, ((W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) := by
          push_cast
          exact Finset.sum_congr rfl fun j _ => l2 j
        have h3 := Finset.add_sum_erase Finset.univ
          (fun j => (W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) (Finset.mem_univ k)
        have h4 : ∑ j, ((W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) =
            ∑ j, (W (InfinitePlace.mk τ)).w j + (n : ℤ) * m (InfinitePlace.mk τ) := by
          rw [Finset.sum_add_distrib]
          simp
        rw [if_pos hv.symm] at hs
        rw [hw, ← hs]
        push_cast at hsum ⊢
        rw [hsum]
        linarith
    · have hn : τ ≠ (InfinitePlace.mk τ).embedding := by
        rw [hv]; exact (conjugate_ne τ).symm
      have l1 : ∀ i, ((lamOf W m τ i : ℕ) : ℤ) = (W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m τ i = ((W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ)).toNat := if_neg hn
        rw [h]
        exact Int.toNat_of_nonneg (hm _ _)
      have l2 : ∀ i, lamOf W m (ComplexEmbedding.conjugate τ) i = m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m (ComplexEmbedding.conjugate τ) i = m (InfinitePlace.mk (ComplexEmbedding.conjugate τ)) :=
          if_pos (by rw [InfinitePlace.mk_conjugate_eq, hv])
        rw [h, InfinitePlace.mk_conjugate_eq]
      have hw : W.at τ = (W (InfinitePlace.mk τ)).dual := if_neg fun h => hn h.symm
      refine ⟨fun i => ((n - 1) * m (InfinitePlace.mk τ) + R) + (lamOf W m τ i + (n - 1 - (i : ℕ))), Fin.rev k,
        Or.inl ⟨m (InfinitePlace.mk τ), fun i => by rw [c2, l2], fun i => ?_⟩, ?_⟩
      · simp only [c1, hR]
      · have e3 : n - 1 - ((Fin.rev k : Fin n) : ℕ) = k := by
          have := k.isLt
          rw [Fin.val_rev]
          omega
        have e4 : (((n - 1 : ℕ) : ℤ)) = (n : ℤ) - 1 := by
          rw [Nat.cast_sub hk]; simp
        rw [if_neg hn] at hs
        rw [hw, ← hs]
        simp only [e3, DomWeight.dual]
        push_cast
        rw [l1, e4]
        ring
