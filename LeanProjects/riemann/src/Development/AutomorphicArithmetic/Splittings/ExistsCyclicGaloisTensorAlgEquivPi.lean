import Mathlib
open scoped TensorProduct
open Polynomial

private lemma comp_eq {F E K A : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    [Field A] [Algebra K A] (f : K ⊗[F] E →ₐ[K] A) :
    ((f : K ⊗[F] E →+* A).comp
        (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom).comp (algebraMap F E) =
      (algebraMap K A).comp (algebraMap F K) := by
  ext c
  have h : (1 : K) ⊗ₜ[F] (algebraMap F E c) = algebraMap K (K ⊗[F] E) (algebraMap F K c) := by
    rw [Algebra.algebraMap_eq_smul_one c, TensorProduct.tmul_smul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one c]
    simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  rw [h, AlgHom.commutes]

private lemma splitting {F E K A : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    [Field A] [Algebra K A] (p : F[X]) [IsSplittingField F E p] (f : K ⊗[F] E →ₐ[K] A)
    (hf : Function.Surjective f) : IsSplittingField K A (p.map (algebraMap F K)) := by
  set ι : E →+* A := (f : K ⊗[F] E →+* A).comp
    (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom with hι
  have hc : ι.comp (algebraMap F E) = (algebraMap K A).comp (algebraMap F K) := comp_eq f
  refine IsSplittingField.mk ?_ ?_
  · have h := (IsSplittingField.splits E p).map ι
    rwa [Polynomial.map_map, hc, ← Polynomial.map_map] at h
  · have h1 := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := K) (p.rootSet E)
      (IsSplittingField.adjoin_rootSet E p)
    have h2 : Algebra.adjoin K (f '' ((fun x : E ↦ (1 : K) ⊗ₜ[F] x) '' p.rootSet E)) = ⊤ := by
      rw [← AlgHom.map_adjoin, h1, Algebra.map_top, AlgHom.range_eq_top]
      exact hf
    refine top_le_iff.1 (h2 ▸ Algebra.adjoin_mono ?_)
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [Polynomial.mem_rootSet] at hx ⊢
    refine ⟨Polynomial.map_ne_zero hx.1, ?_⟩
    have h3 : ι x = f ((1 : K) ⊗ₜ[F] x) := rfl
    rw [← h3, Polynomial.aeval_def, Polynomial.eval₂_map, ← hc, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hx.2, map_zero]

private lemma cyclic {F E K L : Type} [Field F] [Field E] [Algebra F E] [Normal F E]
    [IsCyclic (E ≃ₐ[F] E)] [Field K] [Algebra F K] [Field L] [Algebra K L]
    (f : K ⊗[F] E →ₐ[K] L) (hf : Function.Surjective f) : IsCyclic (L ≃ₐ[K] L) := by
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K L := .of_algebraMap_eq' rfl
  let ι : E →+* L := (f : K ⊗[F] E →+* L).comp
    (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom
  letI : Algebra E L := ι.toAlgebra
  haveI : IsScalarTower F E L := .of_algebraMap_eq' (comp_eq f).symm
  let φ : (L ≃ₐ[K] L) →* (E ≃ₐ[F] E) :=
    (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom F)
  refine isCyclic_of_injective φ ((injective_iff_map_eq_one φ).2 fun g hg ↦ ?_)
  have hfix : ∀ x : E, g (ι x) = ι x := fun x ↦ by
    have h := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars F g) E x
    have h2 : (AlgEquiv.restrictScalars F g).restrictNormal E = 1 := hg
    rw [h2] at h
    exact h.symm
  have hcomp : (g : L →ₐ[K] L).comp f = f := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext x
      exact hfix x
  ext y
  obtain ⟨t, rfl⟩ := hf y
  exact DFunLike.congr_fun hcomp t

theorem UpperTheory.exists_cyclic_galois_tensor_algEquiv_pi :
    ∀ (F E K : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] [Field K] [Algebra F K], ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : IsGalois K L) (I : Type) (_ : Fintype I) (_ : DecidableEq I) (_ : Nonempty I), IsCyclic (L ≃ₐ[K] L) ∧ Nonempty (K ⊗[F] E ≃ₐ[K] (I → L)) := by
  intro F E K _ _ _ _ _ _ _ _
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField F E
  haveI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  haveI : Algebra.FormallyEtale K (K ⊗[F] E) := inferInstance
  obtain ⟨I, hI, Ai, iF, iA, e, hs⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K (K ⊗[F] E)).1 inferInstance
  haveI : Nontrivial (K ⊗[F] E) := inferInstance
  haveI hne : Nonempty I := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact not_subsingleton (K ⊗[F] E) e.toEquiv.subsingleton
  obtain ⟨i0⟩ := hne
  let fi : ∀ i, K ⊗[F] E →ₐ[K] Ai i := fun i ↦ (Pi.evalAlgHom K Ai i).comp (e : K ⊗[F] E →ₐ[K] _)
  have hfi : ∀ i, Function.Surjective (fi i) := fun i ↦
    (Function.surjective_eval i).comp e.surjective
  haveI hsp : ∀ i, IsSplittingField K (Ai i) (p.map (algebraMap F K)) := fun i ↦
    splitting p (fi i) (hfi i)
  let eqv : ∀ i, Ai i ≃ₐ[K] Ai i0 := fun i ↦
    (IsSplittingField.algEquiv (Ai i) (p.map (algebraMap F K))).trans
      (IsSplittingField.algEquiv (Ai i0) (p.map (algebraMap F K))).symm
  haveI hfd : FiniteDimensional K (Ai i0) := IsSplittingField.finiteDimensional _ (p.map (algebraMap F K))
  haveI hgal : IsGalois K (Ai i0) :=
    { to_isSeparable := hs i0, to_normal := Normal.of_isSplittingField (p.map (algebraMap F K)) }
  exact ⟨Ai i0, inferInstance, inferInstance, hfd, hgal, I, Fintype.ofFinite I, Classical.decEq I,
    ⟨i0⟩, cyclic (fi i0) (hfi i0), ⟨e.trans (AlgEquiv.piCongrRight eqv)⟩⟩
