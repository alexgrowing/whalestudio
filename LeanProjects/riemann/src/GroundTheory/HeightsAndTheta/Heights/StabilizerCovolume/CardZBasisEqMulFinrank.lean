import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Covolume
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GramLieEqConjTransposeMul
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights.LowerBoundFree
  Module Matrix
open scoped Matrix ComplexConjugate Kronecker

section Tower

variable {Em : Type} [Field Em] [NumberField Em]

def towerZBasis {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) :
    Basis (Fin ρ × (Em →+* ℂ)) ℤ (Submodule.span (𝓞 Em) (Set.range v)) :=
  ((RingOfIntegers.basis Em).smulTower' (Basis.span hv)).reindex
    (Equiv.prodCongr (Equiv.refl _) (equivReindex Em).symm)

theorem towerZBasis_apply {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) (p : Fin ρ × (Em →+* ℂ)) :
    (towerZBasis hv p : M) = RingOfIntegers.basis Em (equivReindex Em p.2) • v p.1 := by
  simp [towerZBasis, Basis.smulTower'_apply, Basis.span_apply]

theorem mem_span_towerZBasis {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) {x : M} (hx : x ∈ Submodule.span (𝓞 Em) (Set.range v)) :
    x ∈ Submodule.span ℤ (Set.range fun p => (towerZBasis hv p : M)) := by
  have h := congrArg Subtype.val ((towerZBasis hv).sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  rw [← h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem card_zBasis_eq_mul_finrank {N : ℕ} {I : Submodule (𝓞 Em) (Fin N → Em)} {ρ : ℕ} {v : Fin ρ → Fin N → Em}
    (hv : IsNzFamily I ρ v) {m : ℕ} {b : Fin m → Fin N → Em} (hb : IsZBasis I b) :
    m = ρ * finrank ℚ Em := by
  obtain ⟨-, hvI, hli, hidx⟩ := hv
  set J := Submodule.span (𝓞 Em) (Set.range v)
  set t : Fin ρ × (Em →+* ℂ) → Fin N → Em := fun p => (towerZBasis hli p : Fin N → Em)
  have hJI : J ≤ I := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hvI a)
  have htZ : LinearIndependent ℤ t :=
    (towerZBasis hli).linearIndependent.map' J.subtype.toAddMonoidHom.toIntLinearMap
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have htQ : LinearIndependent ℚ t := (LinearIndependent.iff_fractionRing ℤ ℚ).1 htZ
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  have hIQ : ∀ x ∈ I, x ∈ Submodule.span ℚ (Set.range b) := fun x hx =>
    Submodule.span_le_restrictScalars ℤ ℚ _ ((hb.2 x).1 hx)
  have hspan : Submodule.span ℚ (Set.range t) = Submodule.span ℚ (Set.range b) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact hIQ _ (hJI (towerZBasis hli p).2)
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hbk : b k ∈ I := (hb.2 (b k)).2 (Submodule.subset_span ⟨k, rfl⟩)
      have hmem : J.toAddSubgroup.relIndex I.toAddSubgroup • b k ∈ J :=
        AddSubgroup.nsmul_relIndex_mem J.toAddSubgroup (K := I.toAddSubgroup) hbk
      have hmemQ : J.toAddSubgroup.relIndex I.toAddSubgroup • b k ∈ Submodule.span ℚ (Set.range t) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ (mem_span_towerZBasis hli hmem)
      have hk : b k = ((J.toAddSubgroup.relIndex I.toAddSubgroup : ℚ))⁻¹ •
          (J.toAddSubgroup.relIndex I.toAddSubgroup • b k) := by
        rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hidx), one_smul]
      rw [hk]
      exact Submodule.smul_mem _ _ hmemQ
  have h1 := finrank_span_eq_card htQ
  have h2 := finrank_span_eq_card hbQ
  rw [hspan, h2] at h1
  rw [Fintype.card_fin] at h1
  rw [h1, Fintype.card_prod, Fintype.card_fin, NumberField.Embeddings.card]

open Classical in

theorem det_gram_tower_eq {N : ℕ} (f : (Fin N → Em) →+ (Fin N → Em) →+ ℝ) {I : Submodule (𝓞 Em) (Fin N → Em)}
    {ρ : ℕ} {v : Fin ρ → Fin N → Em} (hv : IsNzFamily I ρ v) {m : ℕ} {b : Fin m → Fin N → Em}
    (hb : IsZBasis I b) :
    (Matrix.of fun p q => f (towerZBasis hv.2.2.1 p : Fin N → Em) (towerZBasis hv.2.2.1 q : Fin N → Em)).det =
      ((Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) ^ 2 *
        (Matrix.of fun k l => f (b k) (b l)).det := by
  classical
  have hli := hv.2.2.1
  set J := Submodule.span (𝓞 Em) (Set.range v)
  have hJI : J.toAddSubgroup ≤ I.toAddSubgroup :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hv.2.1 a)
  have hm : Fintype.card (Fin m) = Fintype.card (Fin ρ × (Em →+* ℂ)) := by
    rw [Fintype.card_fin, card_zBasis_eq_mul_finrank hv hb, Fintype.card_prod, Fintype.card_fin,
      NumberField.Embeddings.card]
  let e : Fin m ≃ Fin ρ × (Em →+* ℂ) := Fintype.equivOfCardEq hm
  have hspanI : Submodule.span ℤ (Set.range b) = I.toAddSubgroup.toIntSubmodule := by
    ext x
    exact (hb.2 x).symm
  let B₂ : Basis (Fin ρ × (Em →+* ℂ)) ℤ I.toAddSubgroup.toIntSubmodule :=
    ((Basis.span hb.1).map (LinearEquiv.ofEq _ _ hspanI)).reindex e
  have hB₂ : ∀ k, (B₂ k : Fin N → Em) = b (e.symm k) := by
    intro k
    simp only [B₂, Basis.reindex_apply, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  let eJ : J ≃+ J.toAddSubgroup.toIntSubmodule :=
    { toFun := fun x => ⟨x, x.2⟩, invFun := fun x => ⟨x, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  let B₁ : Basis (Fin ρ × (Em →+* ℂ)) ℤ J.toAddSubgroup.toIntSubmodule :=
    (towerZBasis hli).map eJ.toIntLinearEquiv
  have hidx := AddSubgroup.relIndex_eq_natAbs_det J.toAddSubgroup I.toAddSubgroup hJI B₁ B₂
  rw [Basis.det_apply] at hidx
  set M := B₂.toMatrix fun i => (⟨B₁ i, hJI (SetLike.coe_mem _)⟩ : I.toAddSubgroup.toIntSubmodule)
  have hexp : ∀ p, (towerZBasis hli p : Fin N → Em) = ∑ k, M k p • b (e.symm k) := by
    intro p
    have h := congrArg Subtype.val (B₂.sum_repr ⟨B₁ p, hJI (SetLike.coe_mem _)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hB₂] at h
    have hB₁ : (B₁ p : Fin N → Em) = towerZBasis hli p := rfl
    rw [← hB₁, ← h]
    rfl
  have hgram : (Matrix.of fun p q => f (towerZBasis hli p : Fin N → Em) (towerZBasis hli q : Fin N → Em)) =
      (M.map (Int.cast : ℤ → ℝ))ᵀ * (Matrix.of fun k l => f (b k) (b l)).submatrix e.symm e.symm *
        M.map (Int.cast : ℤ → ℝ) := by
    ext p q
    rw [Matrix.of_apply, hexp p, hexp q]
    simp only [map_sum, map_zsmul, AddMonoidHom.finset_sum_apply, AddMonoidHom.coe_smul, Pi.smul_apply]
    simp only [zsmul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.submatrix_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hc : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det M
    simpa using this.symm
  rw [hgram, det_mul, det_mul, det_transpose, det_submatrix_equiv_self, hidx, Nat.cast_natAbs,
    Int.cast_abs, sq_abs, hc]
  ring

end Tower

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def gramLieAll (z : (Σ k, ι k) → ℂ) {ρ : ℕ} (v : Fin ρ → Fin D.N → Em) (σ : Em →+* ℂ) :
    Matrix (Fin ρ) (Fin ρ) ℂ :=
  Sum.elim (fun τ => D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v)
    (fun τ => (D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v).map (starRingEnd ℂ))
    (D.herm.embEquiv.symm σ)

theorem hodgeInner_tower {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo) {I : Submodule (𝓞 Em) (Fin D.N → Em)}
    (hI : D.herm.IsIso I) {ρ : ℕ} {v : Fin ρ → Fin D.N → Em} (hv : ∀ a, v a ∈ I)
    (hli : LinearIndependent (𝓞 Em) v) (p q : Fin ρ × (Em →+* ℂ)) :
    ((D.hodgeInner z (towerZBasis hli p : Fin D.N → Em) (towerZBasis hli q : Fin D.N → Em) : ℝ) : ℂ) =
      ∑ σ : Em →+* ℂ, star (σ ((RingOfIntegers.basis Em (equivReindex Em p.2) : 𝓞 Em) : Em)) *
        D.gramLieAll z v σ p.1 q.1 * σ ((RingOfIntegers.basis Em (equivReindex Em q.2) : 𝓞 Em) : Em) := by
  have hJI : Submodule.span (𝓞 Em) (Set.range v) ≤ I :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hv a)
  rw [D.hodgeInner_of_iso hz hI (hJI (towerZBasis hli p).2) (hJI (towerZBasis hli q).2)]
  simp only [towerZBasis_apply, HermDatum.lieComp_smul]
  set ωp := ((RingOfIntegers.basis Em (equivReindex Em p.2) : 𝓞 Em) : Em)
  set ωq := ((RingOfIntegers.basis Em (equivReindex Em q.2) : 𝓞 Em) : Em)
  set G := fun τ => D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v
  have hw : ∀ τ, ∑ c, conj (D.herm.emb τ ωp *
        D.herm.lieComp (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ (v p.1) c) *
      (D.herm.emb τ ωq * D.herm.lieComp (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ (v q.1) c) =
      conj (D.herm.emb τ ωp) * D.herm.emb τ ωq * G τ p.1 q.1 := by
    intro τ
    simp only [G, HermDatum.gramLie, Matrix.of_apply, Finset.mul_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp only [hw]
  rw [← D.herm.embEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [gramLieAll, Equiv.symm_apply_apply]
  simp only [Sum.elim_inl, Sum.elim_inr, HermDatum.embEquiv_inl,
    HermDatum.embEquiv_inr, RingHom.comp_apply, Matrix.map_apply, Complex.star_def, Complex.conj_conj]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [show ∀ w : ℂ, (2 : ℂ) * (w.re : ℂ) = w + conj w from fun w => by rw [Complex.add_conj]; push_cast; ring]
  simp only [map_mul, Complex.conj_conj, G]
  ring

open Classical in

theorem gram_tower {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo) {I : Submodule (𝓞 Em) (Fin D.N → Em)}
    (hI : D.herm.IsIso I) {ρ : ℕ} {v : Fin ρ → Fin D.N → Em} (hv : ∀ a, v a ∈ I)
    (hli : LinearIndependent (𝓞 Em) v) :
    Complex.ofRealHom.mapMatrix (Matrix.of fun p q =>
        D.hodgeInner z (towerZBasis hli p : Fin D.N → Em) (towerZBasis hli q : Fin D.N → Em)) =
      ((1 : Matrix (Fin ρ) (Fin ρ) ℂ) ⊗ₖ (basisMatrix Em)ᵀ)ᴴ * blockDiagonal (D.gramLieAll z v) *
        ((1 : Matrix (Fin ρ) (Fin ρ) ℂ) ⊗ₖ (basisMatrix Em)ᵀ) := by
  classical
  ext ⟨a, τ⟩ ⟨b, τ'⟩
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Complex.ofRealHom_eq_coe,
    D.hodgeInner_tower hz hI hv hli]
  simp only [mul_apply, conjTranspose_apply, kroneckerMap_apply, one_apply, transpose_apply,
    blockDiagonal_apply, Fintype.sum_prod_type, basisMatrix_apply']
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, star_zero, apply_ite star,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.star_def]
  rw [Fintype.sum_eq_single b fun x hx ↦ by simp [hx]]
  simp only [if_true]

open Classical in

theorem det_gram_tower {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo) {I : Submodule (𝓞 Em) (Fin D.N → Em)}
    (hI : D.herm.IsIso I) {ρ : ℕ} {v : Fin ρ → Fin D.N → Em} (hv : ∀ a, v a ∈ I)
    (hli : LinearIndependent (𝓞 Em) v) :
    (Matrix.of fun p q =>
        D.hodgeInner z (towerZBasis hli p : Fin D.N → Em) (towerZBasis hli q : Fin D.N → Em)).det =
      |(discr Em : ℝ)| ^ ρ *
        ∏ τ, ((D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v).det.re) ^ 2 := by
  classical
  apply Complex.ofReal_injective
  have hG := congrArg Matrix.det (D.gram_tower hz hI hv hli)
  rw [← RingHom.map_det, Complex.ofRealHom_eq_coe] at hG
  rw [hG, det_mul, det_mul, det_conjTranspose, det_kronecker, det_one, one_pow, one_mul,
    det_transpose, det_blockDiagonal]
  have hB : star (basisMatrix Em).det * (basisMatrix Em).det = ((|(discr Em : ℝ)| : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow, det_basisMatrix_sq]
    simp
  have hP : ∏ σ, (D.gramLieAll z v σ).det =
      ((∏ τ, ((D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v).det.re) ^ 2 : ℝ) : ℂ) := by
    rw [← D.herm.embEquiv.prod_comp, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    push_cast
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [gramLieAll, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det,
      (D.herm.det_gramLie_eq_re (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v).1, Complex.conj_ofReal]
    simp only [Complex.ofReal_re]
    ring
  rw [hP, Fintype.card_fin, star_pow]
  have key : star (basisMatrix Em).det ^ ρ * (basisMatrix Em).det ^ ρ =
      ((|(discr Em : ℝ)| : ℝ) : ℂ) ^ ρ := by
    rw [← mul_pow, hB]
  push_cast at key ⊢
  linear_combination
    (∏ τ, ((D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v).det.re : ℂ) ^ 2) * key

theorem covolZ_eq_of_family {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo) {I : Submodule (𝓞 Em) (Fin D.N → Em)}
    (hI : D.herm.IsIso I) {ρ : ℕ} {v : Fin ρ → Fin D.N → Em} (hv : IsNzFamily I ρ v)
    (hex : ∃ m, ∃ b : Fin m → Fin D.N → Em, IsZBasis I b) :
    D.covolZ z I =
      (∏ τ, (D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v).det.re) /
          ((Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) *
        |(discr Em : ℝ)| ^ ((ρ : ℝ) / 2) := by
  classical
  unfold covolZ
  rw [dif_pos hex]
  have hb := hex.choose_spec.choose_spec
  have h1 := det_gram_tower_eq (D.hodgeAdd z) hv hb
  simp only [hodgeAdd_apply] at h1
  rw [D.det_gram_tower hz hI hv.2.1 hv.2.2.1] at h1
  have hidx : ((Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hv.2.2.2
  have hr : ∀ τ, 0 ≤ (D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v).det.re := fun τ =>
    (D.herm.det_gramLie_eq_re _ _ τ v).2
  have hd : (|(discr Em : ℝ)| ^ ((ρ : ℝ) / 2)) ^ 2 = |(discr Em : ℝ)| ^ ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hdet : (Matrix.of fun k l => D.hodgeInner z (hex.choose_spec.choose k) (hex.choose_spec.choose l)).det =
      ((∏ τ, (D.herm.gramLie (D.j_le.trans (Nat.sub_le _ _)) (D.per z τ) τ v).det.re) /
          ((Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) *
        |(discr Em : ℝ)| ^ ((ρ : ℝ) / 2)) ^ 2 := by
    rw [mul_pow, div_pow, hd, ← Finset.prod_pow]
    field_simp
    linarith [h1]
  rw [hdet, Real.sqrt_sq]
  exact mul_nonneg (div_nonneg (Finset.prod_nonneg fun τ _ => hr τ) (Nat.cast_nonneg _))
    (Real.rpow_nonneg (abs_nonneg _) _)

end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
