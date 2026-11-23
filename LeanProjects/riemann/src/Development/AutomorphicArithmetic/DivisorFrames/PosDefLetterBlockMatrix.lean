import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.GradedNorm
open scoped ComplexOrder

private theorem prod_grSq_eq_det {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) :
    ∏ i, ((grSq M i : ℝ) : ℂ) = M.det := by
  have hp := lminor_pos h
  have h0 : ReciprocityTheory.ChartRestriction.G.FD.lminor M 0 = 1 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
    exact Matrix.det_isEmpty (n := Fin 0)
  have hl : ReciprocityTheory.ChartRestriction.G.FD.lminor M (Fin.last m) = M.det := rfl
  have h1 := (Fin.prod_univ_succ fun k => ReciprocityTheory.ChartRestriction.G.FD.lminor M k).symm.trans
    (Fin.prod_univ_castSucc fun k => ReciprocityTheory.ChartRestriction.G.FD.lminor M k)
  rw [h0, one_mul, hl] at h1
  have h2 : ∀ i : Fin m, ((grSq M i : ℝ) : ℂ) =
      ReciprocityTheory.ChartRestriction.G.FD.lminor M i.succ / ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc := fun i =>
    Complex.ext rfl (Complex.pos_iff.1 (div_pos (hp i.succ) (hp i.castSucc))).2
  simp only [h2]
  rw [Finset.prod_div_distrib, h1, mul_div_cancel_left₀ _ (Finset.prod_ne_zero_iff.2 fun i _ => (hp _).ne')]

theorem UpperTheory.posDef_letter_block_matrix :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), m = (letters Dw).length → (∀ τ, (G τ).PosDef) → (∀ (k k' : Fin m) t b b', (letters Dw)[(k : ℕ)]? = some ⟨t, b⟩ → (letters Dw)[(k' : ℕ)]? = some ⟨t, b'⟩ → M k k' = G t b b') → (∀ (k k' : Fin m) (a a' : Pad.Letter Dw), (letters Dw)[(k : ℕ)]? = some a → (letters Dw)[(k' : ℕ)]? = some a' → a.1 ≠ a'.1 → M k k' = 0) → M.det.re = ∏ z : Pad.Letter Dw, grSq (G z.1) z.2 := by
  intro E _ _ _ H Dw m M G hm hG h1 h2
  classical
  subst hm
  let e := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have hget : ∀ k : Fin (letters Dw).length, (letters Dw)[(k : ℕ)]? = some (e k) := fun k =>
    List.getElem?_eq_getElem k.2
  have hM : M = (Matrix.blockDiagonal' G).submatrix e e := by
    ext k k'
    have a1 := hget k
    have a2 := hget k'
    rw [Matrix.submatrix_apply]
    generalize e k = x at a1 ⊢
    generalize e k' = y at a2 ⊢
    obtain ⟨t, b⟩ := x
    obtain ⟨t', b'⟩ := y
    by_cases ht : t = t'
    · subst ht
      rw [Matrix.blockDiagonal'_apply_eq]
      exact h1 k k' t b b' a1 a2
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ ht]
      exact h2 k k' _ _ a1 a2 ht
  have hd : M.det = ((∏ z : Pad.Letter Dw, grSq (G z.1) z.2 : ℝ) : ℂ) := by
    rw [hM, Matrix.det_submatrix_equiv_self, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod, Complex.ofReal_prod,
      Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun τ _ => (prod_grSq_eq_det (hG τ)).symm
  rw [hd, Complex.ofReal_re]
