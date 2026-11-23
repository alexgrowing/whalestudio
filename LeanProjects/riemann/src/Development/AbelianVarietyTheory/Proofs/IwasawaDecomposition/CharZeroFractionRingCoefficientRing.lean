import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HeightCounting.FracCharZero

theorem injective_of_finite_dvr {A B : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] :
    Function.Injective (algebraMap A B) := by
  rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hker : (⊥ : Ideal B).comap (algebraMap A B) ≠ ⊥ := by
    intro h
    apply ha0
    have : a ∈ (⊥ : Ideal B).comap (algebraMap A B) := by simp [Ideal.mem_comap, ha]
    rw [h] at this
    simpa using this
  have hmax : ((⊥ : Ideal B).comap (algebraMap A B)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hker
  have hbot : (⊥ : Ideal B).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) _ hmax
  exact IsDiscreteValuationRing.not_a_field B (IsLocalRing.eq_maximalIdeal hbot).symm

theorem charZero_of_injective {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [CharZero R]
    (f : R →+* S) (hf : Function.Injective f) : CharZero S :=
  ⟨fun m n h => by
    have : f (m : R) = f (n : R) := by simpa [map_natCast] using h
    exact Nat.cast_injective (hf this)⟩

end GlobalTheory.HeightCounting.FracCharZero

namespace GlobalTheory.HeightCounting

theorem TwR.charZero_fractionRing_O : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw),
    CharZero (FractionRing (T.O i)) := by
  intro D T i
  have h1 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    FracCharZero.injective_of_finite_dvr
  have h2 := T.O_inj i
  have h3 := IsFractionRing.injective (T.O i) (FractionRing (T.O i))
  exact FracCharZero.charZero_of_injective
    (((algebraMap (T.O i) (FractionRing (T.O i))).comp (algebraMap (T.O0 i) (T.O i))).comp
      (algebraMap ℤ_[T.l i] (T.O0 i))) (h3.comp (h2.comp h1))

end GlobalTheory.HeightCounting
