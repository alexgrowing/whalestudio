import Mathlib
open Matrix TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemRankStalk

theorem finrank_range_baseChange_eq {R S M : Type} [CommRing R] [Field S] [Algebra R S]
    [AddCommGroup M] [Module R M] (e : M →ₗ[R] M) (he : e ∘ₗ e = e) :
    Module.finrank S (LinearMap.range (e.baseChange S)) =
      Module.finrank S (S ⊗[R] LinearMap.range e) := by
  let r : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  have hir : e = i ∘ₗ r := LinearMap.ext fun _ => rfl
  have hS : r.baseChange S ∘ₗ i.baseChange S = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hsurj : Function.Surjective (r.baseChange S) := fun x =>
    ⟨i.baseChange S x, LinearMap.congr_fun hS x⟩
  have hinj : Function.Injective (i.baseChange S) := fun x y hxy => by
    have := congrArg (r.baseChange S) hxy
    rwa [← LinearMap.comp_apply, hS, ← LinearMap.comp_apply, hS] at this
  have h2 : e.baseChange S = i.baseChange S ∘ₗ r.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← hir]
  rw [h2, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj),
    LinearMap.finrank_range_of_inj hinj]

theorem finrank_range_map_eq_rankAtStalk (A : Type) [CommRing A] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (k : Type) [Field k] (g : A →+* k) :
    Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
      Module.rankAtStalk (LinearMap.range P.mulVecLin)
        (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  letI : Algebra A k := g.toAlgebra
  set e : (Fin n → A) →ₗ[A] (Fin n → A) := P.mulVecLin with he_def
  have he : e ∘ₗ e = e := by
    rw [he_def, ← Matrix.mulVecLin_mul, hP]

  let r : (Fin n → A) →ₗ[A] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[A] (Fin n → A) := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  haveI : Module.Projective A (LinearMap.range e) := Module.Projective.of_split i r hri

  have hst := Module.rankAtStalk_baseChange (R := A) (M := LinearMap.range e) (S := k) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at hst
  have hcomap : PrimeSpectrum.comap (algebraMap A k) (⊥ : PrimeSpectrum k) =
      (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
    ext x
    change x ∈ Ideal.comap (algebraMap A k) (⊥ : Ideal k) ↔ x ∈ RingHom.ker g
    rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker]
    rfl
  rw [hcomap] at hst
  rw [← hst, ← finrank_range_baseChange_eq e he]

  let Φ : k ⊗[A] (Fin n → A) ≃ₗ[k] (Fin n → k) := TensorProduct.piScalarRight A k k (Fin n)
  have hΦ : ∀ x, Φ (e.baseChange k x) = (P.map g).mulVecLin (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      ext j
      simp [Φ, e, TensorProduct.piScalarRight_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    | add x y hx hy => simp only [map_add, hx, hy]
  have hrange : LinearMap.range (P.map g).mulVecLin =
      (LinearMap.range (e.baseChange k)).map (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) := by
    have hc : (P.map g).mulVecLin ∘ₗ (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) =
        (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) ∘ₗ e.baseChange k :=
      LinearMap.ext fun x => (hΦ x).symm
    rw [← LinearMap.range_comp, ← hc, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range Φ)]
  rw [hrange, LinearEquiv.finrank_map_eq]
  rfl

end GlobalTheory.IdemRankStalk
