import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

section Chart

open CategoryTheory Limits MvPolynomial

end Chart

end UpperTheory.Gal.KunnethLefschetz.G.PX

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem chart_quotient_X_nonZeroDivisor {A : Type} [CommRing A] {D : ℕ} (j : Fin D) :
    IsSMulRegular (MvPolynomial (Fin D) (MvPolynomial (Fin D) A) ⧸
      Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A))
        (Set.range fun k => MvPolynomial.C (MvPolynomial.X k) -
          MvPolynomial.C (MvPolynomial.X j) * MvPolynomial.X k)))
      (MvPolynomial.X j : MvPolynomial (Fin D) A) := by
  classical
  set J : Ideal (MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) :=
    Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A))
      (Set.range fun k => MvPolynomial.C (MvPolynomial.X k) -
        MvPolynomial.C (MvPolynomial.X j) * MvPolynomial.X k)) with hJdef
  have hgen1 : (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) ∈ J :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hgen2 : ∀ k, (MvPolynomial.C (MvPolynomial.X k) - MvPolynomial.C (MvPolynomial.X j) *
      MvPolynomial.X k : MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) ∈ J :=
    fun k => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  let Z : Fin D → Polynomial (MvPolynomial (Fin D) A) :=
    fun k => if k = j then 1 else Polynomial.C (MvPolynomial.X k)
  let θ0 : MvPolynomial (Fin D) A →+* Polynomial (MvPolynomial (Fin D) A) :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun k => Polynomial.X * Z k)
  let Θ : MvPolynomial (Fin D) (MvPolynomial (Fin D) A) →+* Polynomial (MvPolynomial (Fin D) A) :=
    MvPolynomial.eval₂Hom θ0 Z
  let Λ : Polynomial (MvPolynomial (Fin D) A) →+* MvPolynomial (Fin D) (MvPolynomial (Fin D) A) :=
    Polynomial.eval₂RingHom
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) MvPolynomial.X)
      (MvPolynomial.C (MvPolynomial.X j))
  have hZj : Z j = 1 := by simp [Z]
  have hZk : ∀ k, k ≠ j → Z k = Polynomial.C (MvPolynomial.X k) := fun k hk => by simp [Z, hk]
  have hJ : J ≤ RingHom.ker Θ := by
    rw [hJdef, Ideal.span_le]
    rintro x (rfl | ⟨k, rfl⟩)
    · simp [Θ, hZj]
    · simp [Θ, θ0, hZj]
  have hθ : (Ideal.Quotient.mk J).comp (Λ.comp θ0) = (Ideal.Quotient.mk J).comp MvPolynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Λ, θ0]
    · intro k
      by_cases hk : k = j
      · subst hk
        simp [Λ, θ0, hZj]
      · have e := (Ideal.Quotient.eq (I := J)).mpr (hgen2 k)
        simp [Λ, θ0, hZk k hk, e]
  have hΛ : (Ideal.Quotient.mk J).comp (Λ.comp Θ) = Ideal.Quotient.mk J := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have := congrArg (fun F => F c) hθ
      simpa [Θ] using this
    · intro k
      by_cases hk : k = j
      · subst hk
        have e := (Ideal.Quotient.eq (I := J)).mpr hgen1
        simp [Θ, Λ, hZj, e]
      · simp [Θ, Λ, hZk k hk]
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro x hx
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : MvPolynomial.C (MvPolynomial.X j) * g ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (MvPolynomial (Fin D) A)
      (MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) (MvPolynomial (Fin D) (MvPolynomial (Fin D) A) ⧸ J)] at hx
    simpa [Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq] using hx
  have h2 : Θ (MvPolynomial.C (MvPolynomial.X j) * g) = 0 := hJ h1
  have h3 : Polynomial.X * Θ g = 0 := by
    simpa [Θ, θ0, hZj] using h2
  have h4 : Θ g = 0 := by
    refine Polynomial.ext fun n => ?_
    have := congrArg (fun q => Polynomial.coeff q (n + 1)) h3
    simpa [Polynomial.coeff_X_mul] using this
  have h5 := congrArg (fun F => F g) hΛ
  simp only [RingHom.comp_apply, h4, map_zero] at h5
  exact h5.symm

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartNzdAlg :
    ∀ {A E R : Type} [CommRing A] [CommRing E] [CommRing R] {D : ℕ} (p : A →+* E) (ψ : E →+* R) (s : Fin D → E) (y : Fin D → R) (j : Fin D), (MvPolynomial.eval₂Hom p s).Etale → Function.Surjective (MvPolynomial.eval₂Hom ψ y) → RingHom.ker (MvPolynomial.eval₂Hom ψ y) = Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) E) (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * MvPolynomial.X k)) → ψ (s j) ∈ nonZeroDivisors R := by
  intro A E R _ _ _ D p ψ s y j hE hsurj hker
  classical
  letI : Algebra (MvPolynomial (Fin D) A) E := (MvPolynomial.eval₂Hom p s).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) A) E := hE
  have hX : ∀ k, algebraMap (MvPolynomial (Fin D) A) E (MvPolynomial.X k) = s k := fun k => by
    simp [RingHom.algebraMap_toAlgebra]
  set J : Ideal (MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) :=
    Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A))
      (Set.range fun k => MvPolynomial.C (MvPolynomial.X k) -
        MvPolynomial.C (MvPolynomial.X j) * MvPolynomial.X k)) with hJdef
  have hgen1 : (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) ∈ J :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hgen2 : ∀ k, (MvPolynomial.C (MvPolynomial.X k) - MvPolynomial.C (MvPolynomial.X j) *
      MvPolynomial.X k : MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) ∈ J :=
    fun k => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have hreg : IsSMulRegular
      (TensorProduct (MvPolynomial (Fin D) A) E (MvPolynomial (Fin D) (MvPolynomial (Fin D) A) ⧸ J))
      (MvPolynomial.X j : MvPolynomial (Fin D) A) :=
    IsSMulRegular.lTensor E (chart_quotient_X_nonZeroDivisor j)
  let e2 := MvPolynomial.algebraTensorAlgEquiv (MvPolynomial (Fin D) A) (σ := Fin D) E
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := MvPolynomial (Fin D) A) E
    (MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) E J
  let Φ : MvPolynomial (Fin D) E →ₐ[E]
      TensorProduct (MvPolynomial (Fin D) A) E (MvPolynomial (Fin D) (MvPolynomial (Fin D) A) ⧸ J) :=
    (e1.symm.toAlgHom).comp ((Ideal.Quotient.mkₐ E _).comp e2.symm.toAlgHom)
  have key : ∀ g, e2 (Algebra.TensorProduct.includeRight g) =
      MvPolynomial.map (algebraMap (MvPolynomial (Fin D) A) E) g := by
    intro g
    simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul]
  have hΦJ : ∀ g ∈ J, Φ (MvPolynomial.map (algebraMap (MvPolynomial (Fin D) A) E) g) = 0 := by
    intro g hg
    rw [← key g]
    simp only [Φ, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
      AlgEquiv.symm_apply_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hg),
      map_zero]
  have hIΦ : RingHom.ker (MvPolynomial.eval₂Hom ψ y) ≤ RingHom.ker Φ := by
    rw [hker, Ideal.span_le]
    rintro x (rfl | ⟨k, rfl⟩)
    · have := hΦJ _ hgen1
      simpa using this
    · have := hΦJ _ (hgen2 k)
      simpa [hX] using this
  have hΦI : ∀ f, Φ f = 0 → f ∈ RingHom.ker (MvPolynomial.eval₂Hom ψ y) := by
    intro f hf
    have h1 : Ideal.Quotient.mk (J.map (Algebra.TensorProduct.includeRight
        (R := MvPolynomial (Fin D) A) (A := E))) (e2.symm f) = 0 := by
      have := congrArg e1 hf
      simpa [Φ] using this
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 : J.map (Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin D) A) (A := E)) ≤
        (RingHom.ker (MvPolynomial.eval₂Hom ψ y)).comap e2 := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, Ideal.mem_comap, key, hker]
      have hJI : J ≤ (Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) E)
          (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * MvPolynomial.X k))).comap
          (MvPolynomial.map (algebraMap (MvPolynomial (Fin D) A) E)) := by
        rw [hJdef, Ideal.span_le]
        rintro x (rfl | ⟨k, rfl⟩)
        · exact Ideal.subset_span (by simp)
        · exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, by simp [hX]⟩)
      exact hJI hg
    have := h2 h1
    simpa using this
  rw [mem_nonZeroDivisors_iff_right]
  intro r hr
  obtain ⟨f, rfl⟩ := hsurj r
  have h1 : f * MvPolynomial.C (s j) ∈ RingHom.ker (MvPolynomial.eval₂Hom ψ y) := by
    rw [RingHom.mem_ker, map_mul, MvPolynomial.eval₂Hom_C]
    exact hr
  have h2 : Φ (f * MvPolynomial.C (s j)) = 0 := hIΦ h1
  have h3 : (MvPolynomial.X j : MvPolynomial (Fin D) A) • Φ f =
      (MvPolynomial.X j : MvPolynomial (Fin D) A) • 0 := by
    rw [smul_zero, ← h2, map_mul, Algebra.smul_def, mul_comm]
    congr 1
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← hX j,
      ← IsScalarTower.algebraMap_apply]
  have h4 : Φ f = 0 := hreg h3
  have h5 := hΦI f h4
  simpa using h5
