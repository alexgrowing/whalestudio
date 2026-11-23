import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemiHolds
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem prod_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (f : (E →+* ℂ) → ℂ) :
    ∏ τ, f τ = ∏ v : InfinitePlace E, f v.embedding * f (ComplexEmbedding.conjugate v.embedding) := by
  rw [← Finset.prod_fiberwise Finset.univ (fun τ : E →+* ℂ => InfinitePlace.mk τ) f]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hs : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; exact (star_star τ).symm)
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hs, Finset.prod_pair (conjugate_ne v.embedding).symm]

private theorem exists_list {n : ℕ} (p : ℂ[X]) (hm : p.Monic) (hd : p.natDegree = n) (hs : p.Separable) :
    ∃ t : Fin n → ℂ, Function.Injective t ∧ p = ∏ i, (X - C (t i)) := by
  have hsp := IsAlgClosed.splits p
  have hnd := nodup_roots hs
  have hc : p.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, splits_iff_card_roots.1 hsp, hd]
  let e := p.roots.toFinset.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i : ℂ), fun a b h => e.symm.injective (Subtype.ext h), ?_⟩
  have h1 : ∏ i, (X - C ((e.symm i : ℂ))) = ∏ x ∈ p.roots.toFinset, (X - C x) := by
    rw [← Finset.prod_coe_sort p.roots.toFinset (fun x => (X - C x : ℂ[X]))]
    exact Fintype.prod_equiv e.symm _ _ fun _ => rfl
  rw [h1, Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
  exact hsp.eq_prod_roots_of_monic hm

private theorem roots_list {n : ℕ} (t : Fin n → ℂ) :
    (∏ i, (X - C (t i)) : ℂ[X]).roots = Finset.univ.val.map t := by
  have : (∏ i, (X - C (t i)) : ℂ[X]) = ((Finset.univ.val.map t).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [this, roots_multiset_prod_X_sub_C]

theorem UpperTheory.Gal.CertificateRingHomMap.pWtCore_of :
    UpperTheory.Gal.CertificateRingHomMap.TrRho → UpperTheory.Gal.CertificateRingHomMap.TrSch → UpperTheory.Gal.CertificateRingHomMap.SchHom → UpperTheory.Gal.CertificateRingHomMap.CharConj → UpperTheory.Gal.CertificateRingHomMap.WtCore := by
  intro hTr hSch hHom hCC E _ _ _ n W m hm y P y' s hy hsep hy'
  have hex : ∀ v : InfinitePlace E, ∃ t : Fin n → ℂ, Function.Injective t ∧
      y.val.charpoly.map v.embedding = ∏ i, (X - C (t i)) := fun v =>
    exists_list _ ((charpoly_monic _).map _)
      (by rw [(charpoly_monic _).natDegree_map, charpoly_natDegree_eq_dim, Fintype.card_fin]) (hsep.map)
  choose t ht hχ using hex
  have hc := fun v => hCC E n y P s hy v.embedding (t v) (hχ v)
  have hinv : ((y'⁻¹ : GL (Fin n) E)).val = y.valᵀ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy', ← transpose_mul, Units.mul_inv, transpose_one]
  have hgp : ∀ v, (embAll E n y'⁻¹ v).val.charpoly = ∏ i, (X - C (t v i)) := fun v => by
    show (((y'⁻¹ : GL (Fin n) E)).val.map v.embedding).charpoly = _
    rw [hinv, charpoly_map, charpoly_transpose, hχ]
  have h0 : y.val.charpoly.coeff 0 ≠ 0 := by
    intro h
    have h2 := det_eq_sign_charpoly_coeff y.val
    rw [h, mul_zero] at h2
    exact (Matrix.isUnits_det_units y).ne_zero h2
  let g : (E →+* ℂ) → Fin n → ℂ := fun τ i =>
    if τ = (InfinitePlace.mk τ).embedding then (t (InfinitePlace.mk τ) i)⁻¹ else t (InfinitePlace.mk τ) i / ((s : ℚ) : ℂ)
  have gE : ∀ v : InfinitePlace E, g v.embedding = fun i => (t v i)⁻¹ := fun v => by
    funext i
    simp only [g, InfinitePlace.mk_embedding, if_true]
  have gC : ∀ v : InfinitePlace E, g (ComplexEmbedding.conjugate v.embedding) = fun i => t v i / ((s : ℚ) : ℂ) := fun v => by
    funext i
    simp only [g, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg (conjugate_ne v.embedding)]
  have hL : LocalSmoothExtension.Lists (LocalSmoothExtension.invPol y.val.charpoly) g := by
    intro τ
    rw [LocalSmoothExtension.InvRoots_holds E _ h0 τ]
    obtain ⟨v, hv⟩ : ∃ v : InfinitePlace E, τ = v.embedding ∨ τ = ComplexEmbedding.conjugate v.embedding := by
      refine ⟨InfinitePlace.mk τ, ?_⟩
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; exact (star_star τ).symm)
    rcases hv with rfl | rfl
    · rw [gE, UpperTheory.Gal.W2.rts, hχ, roots_list, Multiset.map_map]
      rfl
    · rw [gC, UpperTheory.Gal.W2.rts, (hc v).2, roots_list, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp, inv_div]
  have lE : ∀ v : InfinitePlace E, lamOf W m v.embedding = fun _ => m v := fun v => by
    funext i
    simp only [lamOf, InfinitePlace.mk_embedding, if_true]
  have lC : ∀ v : InfinitePlace E, lamOf W m (ComplexEmbedding.conjugate v.embedding) =
      fun i => ((W v).w i + m v).toNat := fun v => by
    funext i
    simp only [lamOf, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg (conjugate_ne v.embedding)]
  have hs0 : ((s : ℚ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have hpair : ∀ v : InfinitePlace E,
      UpperTheory.Gal.Schur.sch (lamOf W m v.embedding) (g v.embedding) *
        UpperTheory.Gal.Schur.sch (lamOf W m (ComplexEmbedding.conjugate v.embedding)) (g (ComplexEmbedding.conjugate v.embedding)) =
      (((s : ℚ) : ℂ)⁻¹) ^ (∑ i, ((W v).w i + m v).toNat) *
        LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (W v) (embAll E n y'⁻¹ v)) := fun v => by
    have hp0 : (∏ i, t v i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hc v).1 i
    have e1 := (hHom n (fun i => (t v i)⁻¹) (inv_injective.comp (ht v))).2 (m v)
    have e2 := (hHom n (t v) (ht v)).1 (fun i => ((W v).w i + m v).toNat) (((s : ℚ) : ℂ)⁻¹) (inv_ne_zero hs0)
    have e3 := hSch n (W v) (m v) (hm v) (embAll E n y'⁻¹ v) (t v) (ht v) (hgp v)
    have e4 : (fun i => t v i / ((s : ℚ) : ℂ)) = fun i => ((s : ℚ) : ℂ)⁻¹ * t v i := by
      funext i
      rw [div_eq_inv_mul]
    rw [lE, lC, gE, gC, e4, e1, e2, ← e3, Finset.prod_inv_distrib, inv_pow]
    field_simp
  have hJ : ∀ v : InfinitePlace E, ((∑ i, ((W v).w i + m v).toNat : ℕ) : ℤ) = (∑ i, (W v).w i) + n * m v := fun v => by
    push_cast
    rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hm v i), Finset.sum_add_distrib]
    simp
  rw [LocalSmoothExtension.schWEq_of E n (lamOf W m) _ g hL, prod_emb, Finset.prod_congr rfl fun v _ => hpair v, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hJ2 : (∑ v, ((∑ i, (W v).w i) + n * m v)) = ((∑ v, ∑ i, ((W v).w i + m v).toNat : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hJ v]
    push_cast
    rfl
  show LinearMap.trace ℂ _ (((((s⁻¹ : ℚˣ) : ℚ) : ℂ) ^ (∑ v, ((∑ i, (W v).w i) + n * m v))) •
    Representation.dual ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) y') = _
  rw [map_smul, Representation.dual_apply, LinearMap.trace_transpose', hJ2, zpow_natCast]
  have e5 := hTr E n W (embAll E n y'⁻¹)
  have e6 : ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) y'⁻¹ =
      Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (embAll E n y'⁻¹) := rfl
  have e7 : (((s⁻¹ : ℚˣ) : ℚ) : ℂ) = ((s : ℚ) : ℂ)⁻¹ := by push_cast; rfl
  rw [e6, e7, smul_eq_mul, e5]
