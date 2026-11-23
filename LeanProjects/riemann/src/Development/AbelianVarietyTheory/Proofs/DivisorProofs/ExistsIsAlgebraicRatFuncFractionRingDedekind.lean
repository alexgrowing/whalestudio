import Mathlib

namespace GlobalTheory

namespace FracAlgDedekind

open Order

theorem ringKrullDim_le_of_isIntegral {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by
  rcases isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA
  · rw [ringKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  rw [ringKrullDim, Order.krullDim_eq_iSup_length]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R)
    (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact LTSeries.length_le_krullDim L

theorem exists_finite_inj_polynomial (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (hB : ¬ IsField B) :
    ∃ f : Polynomial k →+* B, Function.Injective f ∧ f.Finite := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have : Module.Finite (MvPolynomial (Fin s) k) B := hfin
  have hle := ringKrullDim_le_of_isIntegral (A := MvPolynomial (Fin s) k) (R := B) hg
  have hdim : ringKrullDim (MvPolynomial (Fin s) k) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hB1 : ringKrullDim B ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  rw [hdim] at hle
  have hs1 : s ≤ 1 := by exact_mod_cast hle.trans hB1
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : Algebra.IsIntegral k (MvPolynomial (Fin 0) k) :=
      Algebra.IsIntegral.of_surjective (Algebra.ofId k (MvPolynomial (Fin 0) k))
        (MvPolynomial.C_surjective (Fin 0))
    have : Algebra.IsIntegral k B := Algebra.IsIntegral.trans (MvPolynomial (Fin 0) k)
    exact hB ((Algebra.IsIntegral.isField_iff_isField (algebraMap k B).injective).1
      (Field.toIsField k))
  obtain rfl : s = 1 := by omega
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
    (MvPolynomial.renameEquiv k (Equiv.equivPUnit.{1, 1} (Fin 1))).trans (MvPolynomial.pUnitAlgEquiv k)
  refine ⟨g.toRingHom.comp e.symm.toRingEquiv.toRingHom, hg.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.symm.surjective)

theorem exists_isAlgebraic_ratFunc : ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
    ∃ _ : Algebra (RatFunc k) (FractionRing B), Algebra.IsAlgebraic (RatFunc k) (FractionRing B) := by
  intro k B _ _ _ _ _ hB
  obtain ⟨f, hf, hfin⟩ := exists_finite_inj_polynomial k B hB
  letI : Algebra (Polynomial k) B := f.toAlgebra
  have : Module.Finite (Polynomial k) B := hfin
  have hφ : Function.Injective (algebraMap (Polynomial k) (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial k) B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hf
  letI alg : Algebra (RatFunc k) (FractionRing B) := (IsFractionRing.lift hφ (K := RatFunc k)).toAlgebra
  have : IsScalarTower (Polynomial k) (RatFunc k) (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq fun p => (IsFractionRing.lift_algebraMap hφ p).symm
  have : FaithfulSMul (Polynomial k) B := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : Algebra.IsAlgebraic B (FractionRing B) :=
    IsLocalization.isAlgebraic (FractionRing B) (nonZeroDivisors B)
  have : Algebra.IsAlgebraic (Polynomial k) (FractionRing B) :=
    Algebra.IsAlgebraic.trans (Polynomial k) B (FractionRing B)
  exact ⟨alg, Algebra.IsAlgebraic.extendScalars (R := Polynomial k) (RatFunc.algebraMap_injective k)⟩

end FracAlgDedekind

end GlobalTheory
