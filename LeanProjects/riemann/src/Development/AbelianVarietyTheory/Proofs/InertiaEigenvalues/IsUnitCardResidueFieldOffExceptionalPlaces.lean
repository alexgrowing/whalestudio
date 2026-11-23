import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResidueUnit

theorem card_residueField_coprime {E : Type} [Field E] [NumberField E] (PP : Pl E) (l : ℕ) (hl : l.Prime)
    (hPP : ((l : ℕ) : 𝓞 E) ∉ PP.asIdeal) : Nat.Coprime (Nat.card (kP PP)) l := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  haveI : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot
  letI : Fintype (kP PP) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (kP PP) (ringChar (kP PP))
  rw [Nat.card_eq_fintype_card, hcard]
  refine Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hl).2 ?_)
  intro hpl
  apply hPP
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : ((ringChar (kP PP) : ℕ) : kP PP) = 0 := ringChar.Nat.cast_ringChar
  rw [hpl] at h0
  simpa using h0

theorem natCast_mem_maximalIdeal_of_finite {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [IsLocalRing A] [Algebra O A] [Module.Finite O A] (l : ℕ) (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    ((l : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
  haveI : Algebra.IsIntegral O A := Algebra.IsIntegral.of_finite O A
  have hmax : ((IsLocalRing.maximalIdeal A).comap (algebraMap O A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal A)
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have : ((l : ℕ) : O) ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap O A) := heq ▸ hl
  simpa using this

theorem isUnit_of_coprime {A : Type} [CommRing A] [IsLocalRing A] (q l : ℕ) (h : Nat.Coprime q l)
    (hl : ((l : ℕ) : A) ∈ IsLocalRing.maximalIdeal A) : IsUnit ((q : ℕ) : A) := by
  have hc : IsCoprime ((q : ℤ)) ((l : ℤ)) := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨a, b, hab⟩ := hc
  by_contra hq
  have hq' : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hq
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : A) * ((q : ℕ) : A) + (b : A) * ((l : ℕ) : A)) = 1 := by
    have := congrArg (Int.cast : ℤ → A) hab
    push_cast at this
    exact this
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq') (Ideal.mul_mem_left _ _ hl)

end GlobalTheory.ResidueUnit

open GlobalTheory.ResidueUnit in

theorem GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw) (k : ℕ) (PP : Pl D.host.E) :
    PP ∉ X.S0 i → IsUnit ((Nat.card (kP PP) : ℕ) : X.Ok i k) := by
  intro hP
  have hl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hP (X.twistExcludedPlaces_contains_residueChar i h)
  haveI := X.Ok_fin i k
  exact isUnit_of_coprime _ _ (card_residueField_coprime PP (X.l i) (X.lPrime i).out hl)
    (natCast_mem_maximalIdeal_of_finite (O := X.O i) (X.l i) (X.O_l i))
