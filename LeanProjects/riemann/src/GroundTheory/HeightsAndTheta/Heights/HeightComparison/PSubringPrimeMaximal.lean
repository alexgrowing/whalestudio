import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightSubringPrimeMaximal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Polynomial

theorem subalgebra_isAlgebraic_int {K : Type} [Field K] [NumberField K] (O : Subalgebra ℤ K)
    (y : O) : IsAlgebraic ℤ y := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hK : IsAlgebraic ℤ (y : K) :=
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (y : K))).restrictScalars (R := ℤ)
  exact (isAlgebraic_algHom_iff O.val Subtype.val_injective).mp hK

theorem SubringPrimeMaximal.proof : SubringPrimeMaximal.Statement := by
  intro K _ _ O q hq hq0
  obtain ⟨b, hbq, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
  set J : Ideal ℤ := q.comap (algebraMap ℤ O) with hJ
  have hJ0 : J ≠ ⊥ :=
    Ideal.comap_ne_bot_of_algebraic_mem hb0 hbq (subalgebra_isAlgebraic_int O b)
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hJm : J.IsMaximal := hJp.isMaximal hJ0
  let _ : Field (ℤ ⧸ J) := Ideal.Quotient.field J
  have hJtop : J ≠ ⊤ := hJm.ne_top
  have hint : Algebra.IsIntegral (ℤ ⧸ J) (O ⧸ q) := by
    constructor
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨P, hP0, hPy⟩ := subalgebra_isAlgebraic_int O y
    set Q := P.primPart
    have hQy : aeval y Q = 0 := aeval_primPart_eq_zero hP0 hPy
    have hQmap : Q.map (Ideal.Quotient.mk J) ≠ 0 := by
      intro h
      obtain ⟨g, hg⟩ := (inferInstance : Submodule.IsPrincipal J)
      have hdvd : C g ∣ Q := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have : Q.coeff i ∈ J := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, h, coeff_zero]
        rw [hg, Submodule.mem_span_singleton] at this
        obtain ⟨a, ha⟩ := this
        exact ⟨a, by rw [← ha, smul_eq_mul, mul_comm]⟩
      have hu := isPrimitive_primPart P g hdvd
      apply hJtop
      rw [hg, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
      exact hu
    refine IsAlgebraic.isIntegral ⟨Q.map (Ideal.Quotient.mk J), hQmap, ?_⟩
    have e : Q.map (Ideal.Quotient.mk J) = Q.map (algebraMap ℤ (ℤ ⧸ J)) := rfl
    rw [e, aeval_def, eval₂_map, show (algebraMap (ℤ ⧸ J) (O ⧸ q)).comp (algebraMap ℤ (ℤ ⧸ J)) =
      algebraMap ℤ (O ⧸ q) from RingHom.ext_int _ _, ← aeval_def]
    have := aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ q) y Q
    rw [Ideal.Quotient.mkₐ_eq_mk] at this
    rw [this, hQy, map_zero]
  have hfield : IsField (ℤ ⧸ J) := Field.toIsField _
  exact Ideal.Quotient.maximal_of_isField q
    ((Algebra.IsIntegral.isField_iff_isField (RingHom.injective _)).mp hfield)

end GroundTheory.Heights₂.Heights
