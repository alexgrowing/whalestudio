import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf

noncomputable section

namespace GlobalTheory.CompanionTheory.FixedPointsCM

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

theorem exists_eq_algebraMap_of_sigR_eq {F E K : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (hfin : Module.finrank F E = 2)
    (hσ : ∀ x, σ (σ x) = x) (u : E) (hu : σ u ≠ u) (x : K ⊗[F] E) (hx : sigR K σ x = x) :
    ∃ c : K, x = algebraMap K (K ⊗[F] E) c := by
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h2 : s • (1 : E) + t • σ u = 0 := by
      have := congrArg σ h
      simpa [map_add, map_smul] using this
    have h3 : t • (σ u - u) = 0 := by
      have : t • (σ u - u) = (s • (1 : E) + t • σ u) - (s • (1 : E) + t • u) := by module
      rw [this, h, h2, sub_zero]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact absurd (sub_eq_zero.mp h4) hu
    subst ht
    refine ⟨?_, rfl⟩
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by simp [hfin]
  let b : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  obtain ⟨p, q, hsu⟩ : ∃ p q : F, σ u = p • (1 : E) + q • u := by
    refine ⟨b.repr (σ u) 0, b.repr (σ u) 1, ?_⟩
    have := b.sum_repr (σ u)
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hrel : (p + q * p) • (1 : E) + (q * q - 1) • u = 0 := by
    have h1 : u = p • (1 : E) + q • σ u := by
      have := hσ u
      rw [hsu] at this
      simpa [map_add, map_smul] using this.symm
    rw [hsu] at h1
    have : (p + q * p) • (1 : E) + (q * q - 1) • u = (p • (1 : E) + q • (p • (1 : E) + q • u)) - u := by module
    rw [this, ← h1, sub_self]
  obtain ⟨hp, hq⟩ := LinearIndependent.pair_iff.mp hli _ _ hrel
  have hq' : q = -1 := by
    have : (q - 1) * (q + 1) = 0 := by linear_combination hq
    rcases mul_eq_zero.mp this with h | h
    · exfalso
      have hq1 : q = 1 := sub_eq_zero.mp h
      subst hq1
      have hp0 : p = 0 := by
        have : (2 : F) * p = 0 := by linear_combination hp
        simpa using this
      apply hu
      rw [hsu, hp0]
      simp
    · linear_combination h
  subst hq'
  let B := Algebra.TensorProduct.basis K b
  have hB0 : B 0 = (1 : K) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
  have hB1 : B 1 = (1 : K) ⊗ₜ[F] u := by simp [B, hb1]
  obtain ⟨a, c, hac⟩ : ∃ a c : K, x = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] u := by
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    have := B.sum_repr x
    rw [Fin.sum_univ_two, hB0, hB1] at this
    simpa [TensorProduct.smul_tmul'] using this.symm
  have hs : sigR K σ x = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] σ u := by
    rw [hac]
    simp [sigR]
  have hkey : (algebraMap F K p * c) • B 0 = (c + c) • B 1 := by
    rw [hB0, hB1]
    have h1 : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] σ u = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] u := by rw [← hs, hx, hac]
    have h2 := add_left_cancel h1
    rw [hsu, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, neg_smul, one_smul] at h2
    have e0 : (algebraMap F K p * c) • ((1 : K) ⊗ₜ[F] (1 : E)) = p • (c ⊗ₜ[F] (1 : E)) := by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.smul_def]
    have e1 : (c + c) • ((1 : K) ⊗ₜ[F] u) = c ⊗ₜ[F] u + c ⊗ₜ[F] u := by
      rw [TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
      simp
    rw [e0, e1]
    exact add_neg_eq_iff_eq_add.mp h2
  have hc : c = 0 := by
    have h1 := congrArg (fun y => B.repr y 1) hkey
    simp at h1
    have h2 : (2 : F) • c = 0 := by rw [two_smul]; exact h1.symm
    rcases smul_eq_zero.mp h2 with h | h
    · simp at h
    · exact h
  refine ⟨a, ?_⟩
  rw [hac, hc, Algebra.TensorProduct.algebraMap_apply]
  simp

theorem fixedK : PositivityTheory.SiegelWeilFormula.Gunr.FixedK := by
  intro F E _ _ _ _ _ σ h v x hx
  obtain ⟨-, hC, hfin, hconj⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hconj, hconj, star_star])
  obtain ⟨u, hu⟩ : ∃ u, σ u ≠ u := by
    by_contra hall
    push Not at hall
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hconj τ y
    rw [hall y] at this
    exact this.symm
  exact exists_eq_algebraMap_of_sigR_eq σ hfin hσ u hu x hx

end GlobalTheory.CompanionTheory.FixedPointsCM
