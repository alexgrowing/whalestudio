import Mathlib

set_option autoImplicit false

namespace GlobalTheory.GenericEtale

theorem exists_etale_away_of_isAlgebraic : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A] [CharZero A] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Algebra.Etale A' B' := by
  intro A B _ _ _ _ _ _ _ _ _ _
  haveI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  let K := FractionRing A
  let L := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra A L
  haveI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  haveI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A L := Algebra.IsAlgebraic.trans A B L
  haveI : Algebra.IsAlgebraic K L := (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).1 inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have e1 : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)
  have e2 : Algebra.FormallyEtale K L := .of_isSeparable K L
  have e3 : Algebra.FormallyEtale A L := .comp A K L
  have hl : IsLocalization.AtPrime L (⊥ : Ideal B) := by
    rw [IsLocalization.AtPrime, Ideal.primeCompl_bot]; infer_instance
  have e4 : Algebra.IsEtaleAt A (⊥ : Ideal B) :=
    .of_equiv ((IsLocalization.algEquiv (⊥ : Ideal B).primeCompl L
      (Localization.AtPrime (⊥ : Ideal B))).restrictScalars A)
  obtain ⟨b, hb, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  obtain ⟨h, hh, hd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) b).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero (by simpa using hb))
  refine ⟨h, hh, fun c A' B' _ _ _ _ _ _ _ _ hA' hB' => ?_⟩
  have e5 : Algebra.Etale A (Localization.Away (algebraMap A B (h * c))) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at hE ⊢
    intro x hx
    refine hE fun hxb => hx ?_
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_of_dvd _ hd hxb)
  haveI : Algebra.Etale A B' := .of_equiv ((IsLocalization.algEquiv (.powers (algebraMap A B (h * c)))
    (Localization.Away (algebraMap A B (h * c))) B').restrictScalars A)
  haveI : Algebra.Etale A A' := .of_isLocalizationAway (h * c)
  exact Algebra.Etale.of_restrictScalars A A' B'

end GlobalTheory.GenericEtale
