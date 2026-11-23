import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuation
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.ConjPlace

open GlobalTheory.IdemSupport (cP cO mem_cP cO_cO cO_coe)

theorem conj_smul_eq (D : D7) (x : 𝓞 D.host.E) : D.host.conj • x = cO D x := by
  apply RingOfIntegers.ext
  rw [cO_coe, Formalism.BasicNotions.Examples₂.star_eq_conj]
  rfl

theorem mem_conj_smul (D : D7) (I : Ideal (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (D.host.conj • I : Ideal (𝓞 D.host.E)) ↔ cO D x ∈ I := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : D.host.conj⁻¹ • x = cO D x := by
    rw [inv_smul_eq_iff, conj_smul_eq, cO_cO]
  rw [this]

theorem count_conj (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : (cP w).asIdeal = D.host.conj • w.asIdeal)
    (𝔞 : Ideal (𝓞 D.host.E)) (h : 𝔞 ≠ ⊥) :
    FractionalIdeal.count D.host.E (cP w)
      ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  have h' : (D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) ≠ 0 := fun e => h (by
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e
    simpa using this)
  rw [FractionalIdeal.count_coe _ _ h', FractionalIdeal.count_coe _ _ h]
  congr 1
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 h') (cP w).associates_irreducible,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 h) w.associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le, hw, ← smul_pow', Ideal.pointwise_smul_le_pointwise_smul_iff]

theorem exists_norm (D : D7) (x : 𝓞 D.host.E) :
    ∃ y : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y = x * cO D x := by
  have hm : ((x * cO D x : 𝓞 D.host.E) : D.host.E) ∈ maximalRealSubfield D.host.E := by
    rw [← IsCMField.complexConj_eq_self_iff]
    change star ((x * cO D x : 𝓞 D.host.E) : D.host.E) = _
    rw [← cO_coe, map_mul, cO_cO, mul_comm]
  refine ⟨⟨⟨_, hm⟩, ?_⟩, rfl⟩
  exact (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1 (x * cO D x).isIntegral_coe

theorem cO_algebraMap (D : D7) (y : 𝓞 D.host.F) :
    cO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y := by
  apply RingOfIntegers.ext
  rw [cO_coe]
  exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 (y : D.host.F).2

theorem under_cP (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (cP w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  ext y
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ (cP w).asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w.asIdeal
  rw [mem_cP, cO_algebraMap]

theorem under_eq_iff (D : D7) (w w'' : HeightOneSpectrum (𝓞 D.host.E)) :
    w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = cP w := by
  refine ⟨fun h => ?_, ?_⟩
  · have hs : (w''.asIdeal : Set (𝓞 D.host.E)) ⊆ w.asIdeal ∪ (cP w).asIdeal := fun x hx => by
      obtain ⟨y, hy⟩ := exists_norm D x
      have h1 : y ∈ (w''.under (𝓞 D.host.F)).asIdeal := by
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w''.asIdeal
        rw [hy]; exact Ideal.mul_mem_right _ _ hx
      rw [h] at h1
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y ∈ w.asIdeal at h1
      rw [hy] at h1
      exact w.isPrime.mem_or_mem h1
    exact (Ideal.subset_union.1 hs).imp GlobalTheory.IdemSupport.eq_of_le GlobalTheory.IdemSupport.eq_of_le
  · rintro (rfl | rfl)
    · rfl
    · exact under_cP D w

theorem conj_place : ∀ (D : D7), ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w' := by
  intro D w
  have hw : (cP w).asIdeal = D.host.conj • w.asIdeal := by
    ext x
    rw [mem_cP, mem_conj_smul]
  refine ⟨cP w, hw, fun x => ?_, count_conj D w hw, under_eq_iff D w⟩
  have hc : w = GlobalTheory.CuspRep.conjSrc (D.host.conj : D.host.E ≃+* D.host.E) (cP w) :=
    GlobalTheory.CuspRep.eq_conjSrc fun y => by
      have := GlobalTheory.ConjVal.valuation_cP w y
      rw [Formalism.BasicNotions.Examples₂.star_eq_conj] at this
      exact this
  rw [GlobalTheory.BotFormula.toFinE_sgA]
  refine ((GlobalTheory.CuspRep.conjLoc_spec (D.host.conj : D.host.E ≃+* D.host.E) (cP w)).2.2
    (GlobalTheory.BotFormula.toFinE D x (GlobalTheory.CuspRep.conjSrc (D.host.conj : D.host.E ≃+* D.host.E) (cP w)))).trans ?_
  rw [← hc]

end GlobalTheory.ConjPlace
