import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ExtPrime

open MvPolynomial Filter in
open scoped ENNReal in

theorem _root_.GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L]
    [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K))
    (hP : P.IsPrime) :
    (P.map (MvPolynomial.map (algebraMap K L) :
      MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).IsPrime ∧
    ((∃ j, X j ∉ P) →
      (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
        MvPolynomial (Fin N) L) ∉
      P.map (MvPolynomial.map (algebraMap K L) :
        MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
  classical
  haveI := hP
  let e := (commAlgEquiv K (Fin N) (Fin N)).toRingEquiv
  let ι : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K) :=
    MvPolynomial.map (algebraMap K (MvPolynomial (Fin N) K))
  let π : MvPolynomial (Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K ⧸ P) :=
    (MvPolynomial.map (Ideal.Quotient.mk P)).comp e.toRingHom
  have heι : ∀ p, e (ι p) = C p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [e, ι, commAlgEquiv_C]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p i hp => rw [map_mul, map_mul, hp, map_X]; simp [e, commAlgEquiv_X]
  have hQ : P.map ι = RingHom.ker π := by
    ext b
    rw [RingHom.mem_ker]
    have hb : b = e.symm (e b) := (e.symm_apply_apply b).symm
    constructor
    · intro hb'
      have h1 : P.map ι ≤ RingHom.ker π := by
        rw [Ideal.map_le_iff_le_comap]
        intro p hp
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show MvPolynomial.map (Ideal.Quotient.mk P) (e (ι p)) = 0
        rw [heι p, map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
      exact h1 hb'
    · intro hb'
      have hmem : e b ∈ Ideal.map C P := by
        have hk : Ideal.map (C : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) P =
            RingHom.ker (MvPolynomial.map (σ := Fin N) (Ideal.Quotient.mk P)) := by
          rw [MvPolynomial.ker_map, Ideal.mk_ker]
        rw [hk, RingHom.mem_ker]
        exact hb'
      rw [hb]
      have h2 : Ideal.map e.symm (Ideal.map C P) ≤ P.map ι := by
        rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro p hp
        have h4 : e.symm (C p) = ι p := by
          rw [← heι p]; exact e.symm_apply_apply _
        have h3 : e.symm (C p) ∈ P.map ι := by
          rw [h4]; exact Ideal.mem_map_of_mem ι hp
        exact h3
      exact h2 (Ideal.mem_map_of_mem _ hmem)
  have hQprime : (P.map ι).IsPrime := by rw [hQ]; exact RingHom.ker_isPrime π
  letI : Algebra (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L) :=
    (MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)).toAlgebra
  let Mₛ : Submonoid (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) :=
    Submonoid.map (C : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K))
      (nonZeroDivisors (MvPolynomial (Fin N) K))
  haveI hloc : IsLocalization Mₛ (MvPolynomial (Fin N) L) :=
    MvPolynomial.isLocalization (nonZeroDivisors (MvPolynomial (Fin N) K)) L
  have hdisj : Disjoint (Mₛ : Set (MvPolynomial (Fin N) (MvPolynomial (Fin N) K))) ↑(P.map ι) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    rw [SetLike.mem_coe, hQ, RingHom.mem_ker] at hrQ
    have hπ : π (C r) = MvPolynomial.map (algebraMap K (MvPolynomial (Fin N) K ⧸ P)) r := by
      simp only [π, RingHom.coe_comp, Function.comp_apply]
      rw [show e.toRingHom (C r) = MvPolynomial.map C r from commAlgEquiv_C (R := K) (S₁ := Fin N) r,
        MvPolynomial.map_map]
      rfl
    rw [hπ] at hrQ
    have hinj := MvPolynomial.map_injective (σ := Fin N) _
      (algebraMap K (MvPolynomial (Fin N) K ⧸ P)).injective
    have hr0 : r = 0 := hinj (by rw [hrQ, map_zero])
    exact nonZeroDivisors.ne_zero hr hr0
  have hcomp : (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) =
      (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L)).comp ι := by
    refine RingHom.ext fun p => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, ι, RingHom.algebraMap_toAlgebra, MvPolynomial.map_map]
    rw [← IsScalarTower.algebraMap_eq]
  have hmapeq : P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) =
      (P.map ι).map (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L)) := by
    rw [hcomp, Ideal.map_map]
  rw [hmapeq]
  refine ⟨IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hQprime hdisj, ?_⟩
  rintro ⟨j, hj⟩ hG
  let G₀ : MvPolynomial (Fin N) (MvPolynomial (Fin N) K) := ∑ i : Fin N, C (X i) * X i
  have hG₀ : algebraMap _ (MvPolynomial (Fin N) L) G₀ =
      ∑ i : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X i)) * X i := by
    simp [G₀, RingHom.algebraMap_toAlgebra, map_sum]
  rw [← hG₀] at hG
  have hG₀Q : G₀ ∈ P.map ι := by
    have h := IsLocalization.comap_map_of_isPrime_disjoint _ (MvPolynomial (Fin N) L) hQprime hdisj
    rw [← h]
    exact hG
  rw [hQ, RingHom.mem_ker] at hG₀Q
  have hπG : π G₀ = ∑ i : Fin N, X i * C (Ideal.Quotient.mk P (X i)) := by
    simp only [π, G₀, RingHom.coe_comp, Function.comp_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show e.toRingHom (C (X i)) = X i from commAlgEquiv_C_X (R := K) (S₁ := Fin N) i,
      show e.toRingHom (X i) = C (X i) from commAlgEquiv_X (R := K) (S₂ := Fin N) i, map_X, map_C]
  rw [hπG] at hG₀Q
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single j 1)) hG₀Q
  simp only [coeff_sum, coeff_zero] at hcoeff
  simp_rw [mul_comm (X _), coeff_C_mul, coeff_X', Finsupp.single_left_inj one_ne_zero] at hcoeff
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hcoeff
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)

end GlobalTheory.ExtPrime
