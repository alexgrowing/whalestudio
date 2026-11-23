import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.RestrictScalarsMapEqSpan

open TensorProduct Module

namespace GlobalTheory.GaloisDescent

section Decomposition

variable {ι M M' σ τ : Type*} [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid M']
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M'] [AddSubmonoidClass τ M']

theorem decompose_addMonoidHom (ℳ : ι → σ) (ℳ' : ι → τ) [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition ℳ'] (φ : M →+ M') (hφ : ∀ i, ∀ x ∈ ℳ i, φ x ∈ ℳ' i) (x : M) (i : ι) :
    (DirectSum.decompose ℳ' (φ x) i : M') = φ (DirectSum.decompose ℳ x i) := by
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j x =>
    by_cases h : j = i
    · subst h
      rw [DirectSum.decompose_of_mem_same ℳ' (hφ j _ x.2), DirectSum.decompose_of_mem_same ℳ x.2]
    · rw [DirectSum.decompose_of_mem_ne ℳ' (hφ j _ x.2) h, DirectSum.decompose_of_mem_ne ℳ x.2 h,
        map_zero]
  | add x y hx hy => simp [hx, hy]

end Decomposition

section Ideals

variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}

theorem restrictScalars_map_eq_span (hj : IsBaseChange L j.toLinearMap) (I : Ideal A) :
    (I.map j).restrictScalars L =
      Submodule.span L (j.toLinearMap '' (I.restrictScalars K : Submodule K A)) := by
  first
  | exact @_root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span
  | exact _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span
  | (apply _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span ..)

theorem ideal_comap_map (hj : IsBaseChange L j.toLinearMap) (I : Ideal A) :
    (I.map j).comap j = I := by
  ext a
  have := SetLike.ext_iff.1 (comap_span_image hj (I.restrictScalars K)) a
  rw [← restrictScalars_map_eq_span hj] at this
  exact this

theorem ideal_map_comap_of_span (I : Ideal B) (N : Submodule K A)
    (h : Submodule.span L (j.toLinearMap '' N) = I.restrictScalars L) :
    (I.comap j).map j = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  have hle : Submodule.span L (j.toLinearMap '' N) ≤ ((I.comap j).map j).restrictScalars L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    refine Ideal.mem_map_of_mem j ?_
    exact h.le (Submodule.subset_span ⟨a, ha, rfl⟩)
  exact hle (h.ge hx)

theorem ideal_map_comap_of_stable (hj : IsBaseChange L j.toLinearMap) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → B →+ B) (hφ : ∀ g l a, φ g (l • j a) = s g l • j a)
    (I : Ideal B) (hI : ∀ g, ∀ x ∈ I, φ g x ∈ I) : (I.comap j).map j = I :=
  ideal_map_comap_of_span I _ (span_image_comap_eq hj s hs φ hφ (I.restrictScalars L) hI)

section Graded

variable {ι σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]

theorem isHomogeneous_comap (h : ∀ i, ∀ a ∈ 𝒜 i, j a ∈ ℬ i) {I : Ideal B}
    (hI : I.IsHomogeneous ℬ) : (I.comap j).IsHomogeneous 𝒜 :=
  (HomogeneousIdeal.comap (⟨j.toRingHom, fun {i a} => h i a⟩ : 𝒜 →+*ᵍ ℬ) ⟨I, hI⟩).isHomogeneous

end Graded

end Ideals

section Tensor

open Algebra.TensorProduct

variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

noncomputable def quotientEquivOfMapEq {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) :
    L ⊗[K] (A ⧸ I₀) ≃ₐ[L] (L ⊗[K] A) ⧸ I :=
  (tensorQuotientEquiv (R := K) L A L I₀).trans (Ideal.quotientEquivAlgOfEq L h)

@[simp]
theorem quotientEquivOfMapEq_tmul {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) (l : L) (a : A) :
    quotientEquivOfMapEq I₀ I h (l ⊗ₜ Ideal.Quotient.mk I₀ a) = Ideal.Quotient.mk I (l ⊗ₜ a) :=
  rfl

end Tensor

section Polynomial

open MvPolynomial

variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]

theorem isWeightedHomogeneous_map {M : Type*} [AddCommMonoid M] (w : σ → M) (m : M)
    (f : K →+* L) {p : MvPolynomial σ K} (hp : p.IsWeightedHomogeneous w m) :
    (map f p).IsWeightedHomogeneous w m := fun d hd =>
  hp fun h => hd (by rw [coeff_map, h, map_zero])

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem mvPolynomial_isHomogeneous_comap {I : Ideal (MvPolynomial σ L)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) :
    (I.comap (map (algebraMap K L) : MvPolynomial σ K →+* _)).IsHomogeneous
      (homogeneousSubmodule σ K) :=
  isHomogeneous_comap (j := mapAlgHom (σ := σ) (Algebra.ofId K L)) _ _
    (fun i a ha => isWeightedHomogeneous_map 1 i _ ha) hI

end Polynomial

end GlobalTheory.GaloisDescent
