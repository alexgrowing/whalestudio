import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.NCInhab
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsAvoidProgression
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HostPrimes
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ExistsIsPrimitiveRootIff
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.HeckeCharacterLocalChoice
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDisc
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HvQuadInertia

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

open KStar.Ram DirichletCharacter

private theorem exists_sq_eq_neg_of_quadratic_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hKd : discr K = -(d : ℤ)) : ∃ δ : K, δ ^ 2 = -(d : K) := by
  obtain ⟨x, hx⟩ : ∃ x : K, ∀ c : ℚ, c • (1 : K) ≠ x := by
    by_contra h
    push_neg at h
    have := (finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero).2 h
    omega
  have li : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hx (-(s / t))
      rw [neg_smul, neg_eq_iff_add_eq_zero, ← one_smul ℚ x, ← inv_mul_cancel₀ ht, mul_smul, div_eq_inv_mul, mul_smul, ← smul_add, hst, smul_zero]
  let b := basisOfLinearIndependentOfCardEqFinrank li (by simp [hK])
  have hb : ⇑b = ![(1 : K), x] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  set A := b.repr (x ^ 2) 0
  set B := b.repr (x ^ 2) 1
  have hx2 : x ^ 2 = A • (1 : K) + B • x := by
    conv_lhs => rw [← b.sum_repr (x ^ 2)]
    simp [Fin.sum_univ_two, hb, A, B]
  have hrx : b.repr x = Finsupp.single 1 1 := by
    rw [show x = b 1 by simp [hb]]
    exact b.repr_self 1
  have t1 : Algebra.trace ℚ K 1 = 2 := by
    have := Algebra.trace_algebraMap (R := ℚ) (S := K) 1
    simpa [hK] using this
  have tx : Algebra.trace ℚ K x = B := by
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul]
    simp [hb, hrx, ← sq, B]
  have tx2 : Algebra.trace ℚ K (x ^ 2) = 2 * A + B ^ 2 := by
    rw [hx2, map_add, map_smul, map_smul, t1, tx]
    simp
    ring
  have db : Algebra.discr ℚ b = 4 * A + B ^ 2 := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb, t1, tx, tx2, ← sq]
    ring
  classical
  let I := integralBasis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis I, hK]
  let e := Fintype.equivFinOfCardEq hcard
  let c := b.reindex e.symm
  let P := c.toMatrix I
  have hI : Algebra.discr ℚ I = P.det ^ 2 * Algebra.discr ℚ b := by
    have h1 : Matrix.vecMul (⇑c) (P.map (algebraMap ℚ K)) = ⇑I := c.toMatrix_map_vecMul I
    rw [← h1, Algebra.discr_of_matrix_vecMul]
    congr 1
    rw [Module.Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ b e.symm
  have key : ((Algebra.discr ℚ I : ℚ) : K) = -(d : K) := by
    rw [← coe_discr, hKd]
    push_cast
    ring
  refine ⟨(P.det : K) * (2 * x - B), ?_⟩
  rw [← key, hI, db]
  simp only [Rat.smul_def, mul_one] at hx2
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat]
  linear_combination (4 * (P.det : K) ^ 2) * hx2

private theorem isTotallyComplex_of_quadratic_neg_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hd : d ≠ 0) (hKd : discr K = -(d : ℤ)) : IsTotallyComplex K := by
  have hs := NumberField.sign_discr (K := K)
  rw [hKd] at hs
  have hneg : (-(d : ℤ)).sign = -1 := Int.sign_eq_neg_one_of_neg (by omega)
  rw [hneg, eq_comm, neg_one_pow_eq_neg_one_iff_odd (by decide)] at hs
  obtain ⟨k, hk⟩ := hs
  have hr := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hK] at hr
  apply NumberField.nrRealPlaces_eq_zero_iff.mp
  omega

theorem exists_sq_eq_neg_of_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hd : d ≠ 0) (hKd : discr K = -(d : ℤ)) :
    (∃ δ : K, δ ^ 2 = -(d : K)) ∧ IsTotallyComplex K := ⟨exists_sq_eq_neg_of_quadratic_discr hK hKd, isTotallyComplex_of_quadratic_neg_discr hK hd hKd⟩

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps : DirichletCharacter ℂ N}
  {Y : Subgroup (DirichletCharacter ℂ N)}
  {L : Type} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L]

end KStar.Choice
