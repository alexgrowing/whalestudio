import Mathlib

namespace GlobalTheory.Div.BlockChangeDet

open Matrix

theorem det_blockDiagonal'_eq_prod {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical
  set f := Fintype.equivFin ι
  let b : (Σ c, κ c) → Fin (Fintype.card ι) := fun p => f p.1
  have hb : (Matrix.blockDiagonal' M).BlockTriangular b := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    exact Matrix.blockDiagonal'_apply_ne M i j (fun hc => by subst hc; exact lt_irrefl _ h)
  rw [hb.det_fintype]
  symm
  refine Fintype.prod_equiv f _ _ (fun c => ?_)
  let e : κ c ≃ {p : (Σ c, κ c) // b p = f c} :=
    { toFun := fun i => ⟨⟨c, i⟩, rfl⟩
      invFun := fun p => cast (congrArg κ (f.injective p.2)) p.1.2
      left_inv := fun i => rfl
      right_inv := by
        rintro ⟨⟨c', i⟩, h⟩
        have hc : c' = c := f.injective h
        subst hc
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  exact (Matrix.blockDiagonal'_apply_eq M c i j).symm

theorem det_block_change (F : Type) [Field F] {N : Type} [AddCommGroup N] [Module F N]
    {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N)
    (hℓ : ∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F)
    (hU : ∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) (hA : ∀ k, mu k = ∑ l, A k l • nu l)
    (hg : ∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) :
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  classical

  have hli : LinearIndependent F ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : (0 : N) = ∑ k, (0 : (Σ b, Fin (m b)) → F) k • ℓ k := by simp
    have := (hℓ 0).unique ha.symm h0
    intro i
    exact congrFun this i
  have hsp : ⊤ ≤ Submodule.span F (Set.range ℓ) := by
    intro x _
    obtain ⟨a, ha, -⟩ := hℓ x
    rw [ha]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfr : Module.finrank F N = n := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_congr e, Fintype.card_fin]
  have hspnu : ⊤ ≤ Submodule.span F (Set.range nu) := by
    refine le_trans hsp (Submodule.span_le.mpr ?_)
    rintro _ ⟨σ, rfl⟩
    rw [hU σ]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hlinu : LinearIndependent F nu :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspnu (by simp [hfr])
  have uniq : ∀ a c : Fin n → F, ∑ k, a k • nu k = ∑ k, c k • nu k → a = c := by
    intro a c h
    have := Fintype.linearIndependent_iff.mp hlinu (a - c)
      (by simp [sub_smul, Finset.sum_sub_distrib, h])
    funext k
    exact sub_eq_zero.mp (this k)

  have hdet : U.det ≠ 0 := by
    have hrows : LinearIndependent F (fun i => U i) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hli' : LinearIndependent F (ℓ ∘ e.symm) := hli.comp e.symm e.symm.injective
      refine Fintype.linearIndependent_iff.mp hli' a ?_
      have hcol : ∀ k, ∑ i, a i * U i k = 0 := by
        intro k
        have := congrFun ha k
        simpa [Finset.sum_apply] using this
      calc ∑ i, a i • (ℓ ∘ e.symm) i
          = ∑ i, a i • ∑ k, U i k • nu k := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp [Function.comp, hU]
        _ = ∑ k, (∑ i, a i * U i k) • nu k := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            exact Finset.sum_comm
        _ = 0 := by simp [hcol]
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact (Matrix.isUnit_iff_isUnit_det U |>.mp hu).ne_zero
  refine ⟨hdet, ?_⟩

  have hent : ∀ σ k, ∑ τ, blockDiagonal' g σ τ * U (e τ) k = ∑ l, C σ l * A l k := by
    rintro ⟨b, i⟩
    have h1 : ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ = ∑ j, g b i j • ℓ ⟨b, j⟩ := by
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single b]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [blockDiagonal'_apply_eq]
      · intro b' _ hb'
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [blockDiagonal'_apply_ne g i j (Ne.symm hb'), zero_smul]
      · intro h; exact absurd (Finset.mem_univ b) h
    have h2 : ∑ k, (∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k) • nu k
        = ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ := by
      simp only [hU, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h3 : ∑ k, (∑ l, C ⟨b, i⟩ l * A l k) • nu k = ∑ l, C ⟨b, i⟩ l • mu l := by
      simp only [hA, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have := uniq (fun k => ∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k)
      (fun k => ∑ l, C ⟨b, i⟩ l * A l k) (by rw [h2, h1, hg b i, ← h3])
    intro k
    exact congrFun this k
  have key : Matrix.reindex e e (blockDiagonal' g) * U
      = (Matrix.of fun i k => C (e.symm i) k) * A := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    rw [← hent (e.symm i) k]
    exact Fintype.sum_equiv e.symm _ _ (fun x => by simp)
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, det_blockDiagonal'_eq_prod] at this
  exact this

theorem det_block_change' : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  intro F _ N _ _ κ _ m n e ℓ hℓ nu mu U A C g hU hA hg
  exact det_block_change F m e ℓ hℓ nu mu U A C g hU hA hg

end GlobalTheory.Div.BlockChangeDet
