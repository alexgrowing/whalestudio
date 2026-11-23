import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.NormPrime

open TensorProduct in

theorem norm_one_tmul {A B K : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] [Field K] [Algebra A K] (e : B) :
    Algebra.norm K ((1 : K) ⊗ₜ[A] e : K ⊗[A] B) = algebraMap A K (Algebra.norm A e) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem norm_mem_comap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (e : B) (q : Ideal B) (he : e ∈ q) :
    Algebra.norm A e ∈ q.comap (algebraMap A B) := by
  set χ := (Algebra.lmul A B e).charpoly with hχ
  have h2 : Polynomial.aeval e χ = 0 := by
    apply Algebra.lmul_injective (R := A)
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact LinearMap.aeval_self_charpoly _
  have h3 := congrArg (Polynomial.aeval e) (Polynomial.divX_mul_X_add χ)
  rw [h2, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h3
  have h4 : algebraMap A B (χ.coeff 0) ∈ q := by
    have h5 : algebraMap A B (χ.coeff 0) = -(Polynomial.aeval e χ.divX * e) :=
      eq_neg_of_add_eq_zero_right h3
    rw [h5]
    exact q.neg_mem (q.mul_mem_left _ he)
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_comap.2 h4)

open TensorProduct in

theorem norm_notMem_iff {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (e : B) (p : Ideal A) (hp : p.IsPrime) :
    Algebra.norm A e ∉ p ↔ ∀ q : Ideal B, q.IsPrime → q.comap (algebraMap A B) = p → e ∉ q := by
  constructor
  · intro hN q _ hc he
    exact hN (hc ▸ norm_mem_comap e q he)
  · intro H hN
    have h0 : Algebra.norm p.ResidueField ((1 : p.ResidueField) ⊗ₜ[A] e : p.ResidueField ⊗[A] B) = 0 := by
      rw [norm_one_tmul]
      exact (Ideal.algebraMap_residueField_eq_zero).2 hN
    have hnu : ¬ IsUnit ((1 : p.ResidueField) ⊗ₜ[A] e : p.ResidueField ⊗[A] B) := fun hu => by
      have := hu.map (Algebra.norm p.ResidueField)
      rw [h0] at this
      exact not_isUnit_zero this
    obtain ⟨m, hm, hem⟩ := exists_max_ideal_of_mem_nonunits hnu
    let f : B →ₐ[A] p.ResidueField ⊗[A] B := Algebra.TensorProduct.includeRight
    have hmp : m.IsPrime := hm.isPrime
    refine H (m.comap f) (Ideal.comap_isPrime f m) ?_ (Ideal.mem_comap.2 hem)
    ext a
    have hfa : f (algebraMap A B a) =
        algebraMap p.ResidueField (p.ResidueField ⊗[A] B) (algebraMap A p.ResidueField a) := by
      rw [f.commutes, IsScalarTower.algebraMap_apply A p.ResidueField]
    rw [Ideal.mem_comap, Ideal.mem_comap, hfa]
    constructor
    · intro ha
      by_contra hap
      have hne : algebraMap A p.ResidueField a ≠ 0 :=
        fun h => hap ((Ideal.algebraMap_residueField_eq_zero).1 h)
      exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((isUnit_iff_ne_zero.2 hne).map _))
    · intro ha
      rw [(Ideal.algebraMap_residueField_eq_zero).2 ha, map_zero]
      exact m.zero_mem

end GlobalTheory.CompanionTheory.NormPrime
