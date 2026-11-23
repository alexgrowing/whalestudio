import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal

open MvPolynomial

noncomputable section

namespace GlobalTheory.NormSheaf

theorem map_normForm_eq_prod (K L Ω : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field Ω] [Algebra K Ω] (e : Fin (Module.finrank K L) ≃ (L →ₐ[K] Ω)) {m : ℕ} (x : Fin m → L) :
    (normForm K L x).map (algebraMap K Ω) = ∏ j, ∑ i, C (e j (x i)) * X i := by
  classical
  set b := Module.finBasis K L
  let V : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) Ω := .of fun i k => e i (b k)
  have hV : V.det ≠ 0 := by
    have hli := (linearIndependent_algHom_toLinearMap K L Ω).comp e e.injective
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    refine hc0 (funext (Fintype.linearIndependent_iff.1 hli c (b.ext fun k => ?_)))
    have := congrFun hc k
    simpa [V, Matrix.vecMul, dotProduct] using this
  have key : V.map (C : Ω →+* MvPolynomial (Fin m) Ω) *
      (MvPolynomial.map (algebraMap K Ω)).mapMatrix (∑ i, (X i : MvPolynomial (Fin m) K) •
        (Algebra.leftMulMatrix b (x i)).map (C : K →+* MvPolynomial (Fin m) K)) =
      Matrix.diagonal (fun j => ∑ i, C (e j (x i)) * X i) * V.map (C : Ω →+* MvPolynomial (Fin m) Ω) := by
    ext1 j k
    have h (i : Fin m) : e j (x i) * e j (b k) =
        ∑ l, e j (b l) * algebraMap K Ω (Algebra.leftMulMatrix b (x i) l k) := by
      rw [← map_mul, ← b.sum_repr (x i * b k), map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, Algebra.leftMulMatrix_eq_repr_mul, Algebra.smul_def, mul_comm]
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [V, Matrix.of_apply, Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, map_X, map_C, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, ← C_mul, h, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [C_mul]
    ring
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    ← RingHom.map_det] at hd
  rw [normForm, mul_right_cancel₀ (C_eq_zero.not.2 hV) hd]

end GlobalTheory.NormSheaf

noncomputable section

namespace GlobalTheory.NormSheaf

theorem exists_finite_split_normForm : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R), Function.Injective (algebraMap A R) ∧ Module.Finite A R ∧
      ∃ σ : Fin (Module.finrank K L) → (B →+* R), (∀ j, (σ j).comp φ = algebraMap A R) ∧
        ∀ (m : ℕ) (g : Fin m → B), ∃ P : MvPolynomial (Fin m) A,
          P.map (algebraMap A K) = GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i)) ∧
          P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ hcomp
  classical
  letI : Algebra A B := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  have hcard : Fintype.card (L →ₐ[K] AlgebraicClosure K) = Module.finrank K L := AlgHom.card K L _
  let e : Fin (Module.finrank K L) ≃ (L →ₐ[K] AlgebraicClosure K) := (Fintype.equivFinOfCardEq hcard).symm
  have hAΩ : algebraMap A (AlgebraicClosure K) = (algebraMap K (AlgebraicClosure K)).comp (algebraMap A K) :=
    IsScalarTower.algebraMap_eq A K _

  let F : Fin (Module.finrank K L) → (B →ₐ[A] AlgebraicClosure K) := fun j =>
    { ((e j).toRingHom.comp (algebraMap B L)) with
      commutes' := fun a => by
        have h1 := congrArg (fun f => f a) hcomp
        simp only [RingHom.coe_comp, Function.comp_apply] at h1
        change e j (algebraMap B L (φ a)) = _
        rw [← h1, AlgHom.commutes, hAΩ, RingHom.comp_apply] }
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  let S : Set (AlgebraicClosure K) := Set.range fun p : Fin (Module.finrank K L) × s => F p.1 p.2
  let R : Subalgebra A (AlgebraicClosure K) := Algebra.adjoin A S
  have hSfin : S.Finite := Set.finite_range _
  have hSint : ∀ y ∈ S, IsIntegral A y := by
    rintro _ ⟨p, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := A) (p.2 : B)).map (F p.1)
  have hRfin : Module.Finite A R := by
    exact Module.Finite.iff_fg.mpr (fg_adjoin_of_finite hSfin hSint)
  have hmem : ∀ j (y : B), F j y ∈ R := by
    intro j y
    have hy : y ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz => exact Algebra.subset_adjoin ⟨(j, ⟨z, hz⟩), rfl⟩
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact R.add_mem hu hv
    | smul a u _ hu => rw [map_smul]; exact R.smul_mem hu a
  let σ : Fin (Module.finrank K L) → (B →+* R) := fun j => ((F j).codRestrict R (hmem j)).toRingHom
  have hinjAΩ : Function.Injective (algebraMap A (AlgebraicClosure K)) := by
    rw [hAΩ]
    exact (algebraMap K _).injective.comp (IsFractionRing.injective A K)
  have hval : (algebraMap R (AlgebraicClosure K)).comp (algebraMap A R) = algebraMap A (AlgebraicClosure K) :=
    (IsScalarTower.algebraMap_eq A R _).symm
  refine ⟨R, inferInstance, inferInstance, ?_, hRfin, σ, ?_, ?_⟩
  · intro a b hab
    apply hinjAΩ
    rw [← hval, RingHom.comp_apply, RingHom.comp_apply, hab]
  · intro j
    ext a
    exact congrArg Subtype.val (((F j).codRestrict R (hmem j)).commutes a)
  · intro m g
    let Q : MvPolynomial (Fin m) R := ∏ j, ∑ i, C (σ j (g i)) * X i
    have hQ : Q.map (algebraMap R (AlgebraicClosure K)) =
        (normForm K L (fun i => algebraMap B L (g i))).map (algebraMap K (AlgebraicClosure K)) := by
      rw [map_normForm_eq_prod K L _ e]
      simp only [Q, map_prod, map_sum, map_mul, map_C, map_X]
      rfl
    set N := normForm K L (fun i => algebraMap B L (g i))
    have hcoef : ∀ n, ∃ a : A, algebraMap A K a = N.coeff n := by
      intro n
      have h1 : algebraMap K (AlgebraicClosure K) (N.coeff n) = algebraMap R (AlgebraicClosure K) (Q.coeff n) := by
        rw [← coeff_map, ← coeff_map, hQ]
      have h2 : IsIntegral A (algebraMap R (AlgebraicClosure K) (Q.coeff n)) :=
        (Algebra.IsIntegral.isIntegral (R := A) (Q.coeff n)).map (IsScalarTower.toAlgHom A R (AlgebraicClosure K))
      rw [← h1] at h2
      have h3 : IsIntegral A (N.coeff n) :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K (AlgebraicClosure K)) (algebraMap K _).injective).1 h2
      exact IsIntegrallyClosed.isIntegral_iff.1 h3
    have hrange : N ∈ Set.range (MvPolynomial.map (algebraMap A K)) := by
      rw [mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact hcoef n
    obtain ⟨P, hP⟩ := hrange
    refine ⟨P, hP, ?_⟩
    apply map_injective (algebraMap R (AlgebraicClosure K)) Subtype.val_injective
    rw [map_map, hval, hQ, ← hP, map_map, hAΩ]

end GlobalTheory.NormSheaf
