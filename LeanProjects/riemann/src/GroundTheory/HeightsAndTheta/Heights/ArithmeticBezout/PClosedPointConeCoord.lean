import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointConeCoord
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem aeval_cone_of_isHomogeneous {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n d : ℕ}
    (y : Fin n → Ω) {p : MvPolynomial (Fin n) F} (hp : p.IsHomogeneous d) :
    aeval (fun j => Polynomial.C (y j) * Polynomial.X) p =
      Polynomial.C (aeval y p) * Polynomial.X ^ d := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, ← map_pow,
    ← map_prod, Polynomial.algebraMap_apply, map_mul, mul_assoc]

theorem ClosedPointConeCoord.proof : ClosedPointConeCoord.Statement := by
  intro F _ n I i hI hdim hXi Ω _ _ y hy hyI
  classical
  let φ : MvPolynomial (Fin n) F →ₐ[F] Polynomial Ω :=
    aeval fun j => Polynomial.C (y j) * Polynomial.X
  let P : Ideal (MvPolynomial (Fin n) F) := RingHom.ker φ
  have hPprime : P.IsPrime := RingHom.ker_isPrime _
  have hIP : I ≤ P := by
    intro g hg
    show φ g = 0
    rw [← sum_homogeneousComponent g, map_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [show φ (homogeneousComponent d g) = _ from
      aeval_cone_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g),
      hyI _ (hI.isHomog g hg d), map_zero, zero_mul]
  let m : Ideal (MvPolynomial (Fin n) F) := RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F)
  have hmprime : m.IsPrime := RingHom.ker_isPrime _
  have key : (Polynomial.evalRingHom (0 : Ω)).comp (φ : MvPolynomial (Fin n) F →+* Polynomial Ω) =
      (algebraMap F Ω).comp constantCoeff := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp [φ]
  have hPm : P ≤ m := by
    intro g hg
    have hg' : φ g = 0 := hg
    have h0 := RingHom.congr_fun key g
    simp only [RingHom.comp_apply, RingHom.coe_coe, hg', map_zero] at h0
    show constantCoeff g = 0
    exact (algebraMap F Ω).injective (by rw [← h0, map_zero])
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have hXjP : X j ∉ P := by
    intro h
    have h' : φ (X j) = 0 := h
    simp only [φ, aeval_X] at h'
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hj) Polynomial.X_ne_zero h'
  have hXjm : X j ∈ m := by
    show constantCoeff (X j : MvPolynomial (Fin n) F) = 0
    simp
  have hPlt : P < m := lt_of_le_of_ne hPm fun h => hXjP (h ▸ hXjm)
  have hIeq : I = P := by
    by_contra hne
    have hIlt : I < P := lt_of_le_of_ne hIP hne
    have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
      rw [ringKrullDim_quotient, Order.le_krullDim_iff]
      let a : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨I, hI.isPrime⟩, fun _ h => h⟩
      let b : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨P, hPprime⟩, fun _ h => hIP h⟩
      let c : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨m, hmprime⟩, fun _ h => hPm (hIP h)⟩
      have hab : a < b := hIlt
      have hbc : b < c := hPlt
      exact ⟨LTSeries.mk 2 ![a, b, c]
        (Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exacts [hab, hbc]), rfl⟩
    rw [hdim] at h2
    norm_num at h2
  intro hyi
  apply hXi
  rw [hIeq]
  show φ (X i) = 0
  simp [φ, hyi]

end ObjectsChow

end GroundTheory.Heights₂.Heights
