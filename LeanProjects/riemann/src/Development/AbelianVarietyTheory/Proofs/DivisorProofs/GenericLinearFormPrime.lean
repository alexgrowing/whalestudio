import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm

open MvPolynomial TensorProduct

noncomputable section

namespace GlobalTheory.GenericForm

variable (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (N : ℕ)

def polyEquiv : MvPolynomial (Fin N) k ⊗[k] A ≃+* MvPolynomial (Unit × Fin N) A :=
  ((Algebra.TensorProduct.comm k (MvPolynomial (Fin N) k) A).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv k A).toRingEquiv).trans
    (renameEquiv A (Equiv.punitProd (Fin N)).symm).toRingEquiv

theorem polyEquiv_X_tmul (i : Fin N) (x : A) :
    polyEquiv k A N (X i ⊗ₜ x) = C x * X ((), i) := by
  simp [polyEquiv, smul_eq_C_mul]

theorem polyEquiv_one_tmul (x : A) : polyEquiv k A N (1 ⊗ₜ x) = C x := by
  simp [polyEquiv, smul_eq_C_mul]

variable {k A N}

def genForm (a : Fin N → A) : MvPolynomial (Fin N) k ⊗[k] A := ∑ i, X i ⊗ₜ a i

theorem polyEquiv_genForm (a : Fin N → A) :
    polyEquiv k A N (genForm (k := k) a) = linForm a () := by
  simp [genForm, linForm, map_sum, polyEquiv_X_tmul]

theorem isDomain_tensor : IsDomain (MvPolynomial (Fin N) k ⊗[k] A) :=
  Function.Injective.isDomain (polyEquiv k A N).toRingHom
    (polyEquiv k A N).injective

theorem genForm_ne_zero (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) :
    genForm (k := k) a ≠ 0 := by
  intro h
  have h1 := congrArg (polyEquiv k A N) h
  rw [polyEquiv_genForm, map_zero, ← linFormEquiv_X_of_mem (ι := Unit) a hu (Set.mem_univ ())] at h1
  exact X_ne_zero _ ((linFormEquiv a Set.univ j hu).injective (h1.trans (map_zero _).symm))

theorem map_span_genForm (a : Fin N → A) :
    (Ideal.span {genForm (k := k) a}).map (polyEquiv k A N) = Ideal.span {linForm a ()} := by
  rw [Ideal.map_span, Set.image_singleton, polyEquiv_genForm]

theorem isPrime_span_genForm (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) :
    (Ideal.span {genForm (k := k) a}).IsPrime := by
  have hp : (Ideal.span {linForm a ()}).IsPrime := by
    have := isPrime_span_linForm (ι := Unit) a hu Set.univ
    rwa [Set.image_univ, Set.range_unique] at this
  have : Ideal.span {genForm (k := k) a} =
      (Ideal.span {linForm a ()}).map (polyEquiv k A N).symm := by
    rw [Ideal.map_span, Set.image_singleton, ← polyEquiv_genForm (k := k) a, RingEquiv.symm_apply_apply]
  rw [this]
  exact Ideal.map_isPrime_of_equiv _

theorem eq_zero_of_one_tmul_mem (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) {x : A}
    (hx : (1 : MvPolynomial (Fin N) k) ⊗ₜ[k] x ∈ Ideal.span {genForm (k := k) a}) : x = 0 := by
  have h1 := Ideal.mem_map_of_mem (polyEquiv k A N) hx
  rw [map_span_genForm, polyEquiv_one_tmul] at h1
  have h2 : C x ∈ RingHom.ker (linFormElim a hu (Set.univ : Set Unit)) := by
    rw [ker_linFormElim, Set.image_univ, Set.range_unique]
    exact h1
  rw [RingHom.mem_ker, algHom_C, algebraMap_eq, C_eq_zero] at h2
  exact h2

theorem span_genericForm_isPrime_or_eq_top :
    ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (N : ℕ) (a : Fin N → A)
      (j : Fin N), IsUnit (a j) → ∀ t : FractionRing (MvPolynomial (Fin N) k) ⊗[k] A,
      t = ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k))
        (MvPolynomial.X i) ⊗ₜ[k] a i →
      t ≠ 0 ∧ (Ideal.span {t} = ⊤ ∨ (Ideal.span {t}).IsPrime ∧
        ∀ x : A, (1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] x ∈ Ideal.span {t} → x = 0) := by
  intro k A _ _ _ _ N a j hu t ht
  let P := MvPolynomial (Fin N) k
  let K := FractionRing P
  let B := P ⊗[k] A
  haveI : IsDomain B := isDomain_tensor
  let φ : B →ₐ[k] K ⊗[k] A :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)
  letI : Algebra B (K ⊗[k] A) := φ.toRingHom.toAlgebra
  have hφ : ∀ x, algebraMap B (K ⊗[k] A) x = φ x := fun _ => rfl
  haveI : IsScalarTower P B (K ⊗[k] A) := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    rw [hφ]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have H : (algebraMap B (K ⊗[k] A)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    change φ (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  let M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors P)
  haveI hL : IsLocalization M (K ⊗[k] A) :=
    IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K H
  have hkA : Function.Injective (algebraMap k A) := (algebraMap k A).injective
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨p, hp, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp ?_
    refine Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := P) (B := A) hkA ?_
    rw [map_zero]
    exact h
  have hinj : Function.Injective (algebraMap B (K ⊗[k] A)) := IsLocalization.injective _ hM
  have ht0 : t = algebraMap B (K ⊗[k] A) (genForm (k := k) a) := by
    rw [ht, hφ, genForm, map_sum]
    rfl
  have hspan : Ideal.span {t} = (Ideal.span {genForm (k := k) a}).map (algebraMap B (K ⊗[k] A)) := by
    rw [Ideal.map_span, Set.image_singleton, ht0]
  refine ⟨?_, ?_⟩
  · rw [ht0]
    exact fun h => genForm_ne_zero (k := k) a hu (hinj (h.trans (map_zero _).symm))
  haveI hQ := isPrime_span_genForm (k := k) a hu
  by_cases hd : Disjoint (M : Set B) (Ideal.span {genForm (k := k) a} : Set B)
  · right
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hspan]
      exact IsLocalization.isPrime_of_isPrime_disjoint M (K ⊗[k] A) _ hQ hd
    · have h1 : (1 : K) ⊗ₜ[k] x = algebraMap B (K ⊗[k] A) ((1 : P) ⊗ₜ[k] x) := by
        rw [hφ, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      rw [h1, hspan] at hx
      have h2 := IsLocalization.under_map_of_isPrime_disjoint M (K ⊗[k] A) hQ hd
      have h3 : (1 : P) ⊗ₜ[k] x ∈ ((Ideal.span {genForm (k := k) a}).map
          (algebraMap B (K ⊗[k] A))).under B := hx
      rw [h2] at h3
      exact eq_zero_of_one_tmul_mem a hu h3
  · left
    obtain ⟨m, hmM, hmQ⟩ := Set.not_disjoint_iff.1 hd
    rw [hspan]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmQ)
      (IsLocalization.map_units (K ⊗[k] A) (⟨m, hmM⟩ : M))

end GlobalTheory.GenericForm
