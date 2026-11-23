import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Blockdet

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

@[to_additive]
private theorem UpperTheory.V.KT.prod_emb (L : Type) [Field L] [NumberField L] [IsTotallyComplex L]
    {M : Type} [CommMonoid M] (f : (L →+* ℂ) → M) :
    ∏ φ, f φ = ∏ w : InfinitePlace L, (f w.embedding * f (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk f]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro e
    have := IsTotallyComplex.isComplex w
    rw [InfinitePlace.isComplex_iff] at this
    exact this (ComplexEmbedding.isReal_iff.mpr e.symm)
  rw [← Finset.prod_pair hne]
  congr 1
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rw [← InfinitePlace.mk_embedding w, eq_comm, InfinitePlace.mk_eq_iff] at h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

private theorem UpperTheory.V.KT.det_emb (L : Type) [Field L] [NumberField L] :
    star (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)).det *
      (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)).det =
      (absD L : ℂ) := by
  classical
  have hE : (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) =
      ((basisMatrix L).submatrix (equivReindex L).symm (equivReindex L).symm)ᵀ := by
    ext k i
    simp [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rw [hE, det_transpose, det_submatrix_equiv_self]
  have h := congrArg norm (discr_eq_basisMatrix_det_sq L)
  rw [norm_pow, Complex.norm_intCast] at h
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← h, absD, ← Int.cast_abs,
    ← Int.natCast_natAbs]
  rw [Int.cast_natCast, Complex.ofReal_natCast]

theorem UpperTheory.V.KT.gramdet :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (h : HS L N),
    2 ^ dd L N * (gram h).det = (absD L : ℝ) ^ N * (∏ w, (mat h w).det.re) ^ 2 := by
  intro L _ _ _ N h
  classical
  let A : (L →+* ℂ) → Matrix (Fin N) (Fin N) ℂ := fun φ =>
    if φ = (InfinitePlace.mk φ).embedding then mat h (InfinitePlace.mk φ)
    else (mat h (InfinitePlace.mk φ))ᵀ
  have hne : ∀ w : InfinitePlace L, ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
    intro w e
    have := IsTotallyComplex.isComplex w
    rw [InfinitePlace.isComplex_iff] at this
    exact this (ComplexEmbedding.isReal_iff.mpr e)
  have hA1 : ∀ w : InfinitePlace L, A w.embedding = mat h w := by
    intro w; simp [A, InfinitePlace.mk_embedding]
  have hA2 : ∀ w : InfinitePlace L, A (ComplexEmbedding.conjugate w.embedding) = (mat h w)ᵀ := by
    intro w; simp only [A, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg (hne w)]
  have key := UpperTheory.V.KT.blockdet (BI L) N
    (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L))
    (fun k => A ((equivReindex L).symm k))
  rw [UpperTheory.V.KT.det_emb, Equiv.prod_comp (equivReindex L).symm (fun φ => (A φ).det),
    UpperTheory.V.KT.prod_emb L] at key
  have hM : (Matrix.of fun s t : Fin N × BI L => ∑ k,
      star ((Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) k s.2) *
        A ((equivReindex L).symm k) s.1 t.1 *
        (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) k t.2) =
      Complex.ofRealHom.mapMatrix ((2 : ℝ) • gram h) := by
    ext s t
    simp only [of_apply]
    rw [Equiv.sum_comp (equivReindex L).symm (fun φ => star (φ (RingOfIntegers.basis L s.2 : L)) *
      A φ s.1 t.1 * φ (RingOfIntegers.basis L t.2 : L)), UpperTheory.V.KT.sum_emb L]
    simp only [hA1, hA2, RingHom.mapMatrix_apply, map_apply, Matrix.smul_apply, gram, of_apply,
      smul_eq_mul, Finset.mul_sum, map_sum, Complex.ofRealHom_eq_coe]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Complex.add_conj]
    have hh : mat h w t.1 s.1 = star (mat h w s.1 t.1) := ((mat_herm h w).apply t.1 s.1).symm
    simp [embO, hh, ComplexEmbedding.conjugate_coe_eq]
  rw [hM, ← RingHom.map_det, det_smul] at key
  have hc : Fintype.card (Fin N × BI L) = dd L N := by
    rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank, mul_comm]
  have hd : ∀ w, (mat h w).det = ((mat h w).det.re : ℂ) := by
    intro w
    have : star (mat h w).det = (mat h w).det := by
      rw [← det_conjTranspose, (mat_herm h w).eq]
    exact (Complex.conj_eq_iff_re.mp this).symm
  simp only [hA1, hA2, det_transpose, hc] at key
  rw [Finset.prod_congr rfl fun w _ => by rw [hd w]] at key
  apply Complex.ofReal_injective
  rw [← Complex.ofRealHom_eq_coe, key, Finset.prod_mul_distrib]
  push_cast
  ring
