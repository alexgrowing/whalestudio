import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeHeckeCharOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePlaceUnram

open GlobalTheory.IdemSupport GlobalTheory.LevelPlaces GlobalTheory.SplitOffPlaces

theorem cP_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem unramOutside_mu0_of_splitSet : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → SplitSet L.Pg → ∀ j : Fin D.R.m, UnramOutside (L.mu0 ((j : ℕ) + 1)) L.Pg := by
  intro D T0 L μ0 hL hS j x hinf h1 h2 hx
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hk : ∀ PP ∈ L.Pg, idemAt PP * idem L.Pg = idemAt PP := fun l hl =>
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hS.isIdemAt ha).1) (fun a ha b hb hab => hS.mul_eq_zero ha hb hab) hl
  have hc0 : ∀ PP ∈ L.Pg, idemAt PP * cA D (idem L.Pg) = 0 := fun PP hPP => by
    rw [idem, map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi => hS.mul_conj hPP hi
  have hc1 : ∀ PP ∈ L.Pg, cA D (idemAt PP) * idem L.Pg = 0 := fun PP hPP => by
    rw [idem, Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [mul_comm]; exact hS.mul_conj hi hPP
  have hx1 : ∀ PP ∈ L.Pg, Φ (x : AE D) PP = 1 ∧ Φ (x : AE D) (cP PP) = 1 := fun PP hPP => by
    have hd := delta_of_isIdemAt hΦ (hS.isIdemAt hPP)
    have hd' := delta_conj hΦ hd
    have a : idemAt PP * (x : AE D) = idemAt PP := by
      have e : idemAt PP * (idem L.Pg + cA D (idem L.Pg)) = idemAt PP := by rw [mul_add, hk PP hPP, hc0 PP hPP, add_zero]
      calc idemAt PP * (x : AE D) = idemAt PP * (idem L.Pg + cA D (idem L.Pg)) * x := by rw [e]
        _ = idemAt PP * (idem L.Pg + cA D (idem L.Pg)) := by rw [mul_assoc, hx]
        _ = idemAt PP := e
    have b : cA D (idemAt PP) * (x : AE D) = cA D (idemAt PP) := by
      have e : cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) = cA D (idemAt PP) := by
        rw [mul_add, hc1 PP hPP, zero_add, ← map_mul, hk PP hPP]
      calc cA D (idemAt PP) * (x : AE D) = cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) * x := by rw [e]
        _ = cA D (idemAt PP) * (idem L.Pg + cA D (idem L.Pg)) := by rw [mul_assoc, hx]
        _ = cA D (idemAt PP) := e
    constructor
    · have h := congrArg (fun z => Φ z PP) a
      rwa [ev_mul, hd.2.1, one_mul] at h
    · have h := congrArg (fun z => Φ z (cP PP)) b
      rwa [ev_mul, hd'.2.1, one_mul] at h
  have hg : ∀ k, (D.host.g k : D.host.E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  set m : ℕ := D.host.g 0 * D.host.g 1 with hmdef
  have hm0 : (m : D.host.E) ≠ 0 := by rw [hmdef, Nat.cast_mul]; exact mul_ne_zero (hg 0) (hg 1)
  have hunr : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → (L.C.mu0 j).UnrAt P :=
    fun P hP => (L.C.isMu0 j).unr P fun k hk => hP (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hk
      rw [hmdef, Nat.cast_mul]
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk'
      · exact Ideal.mul_mem_left _ _ hk')
  refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ (L.C.mu0 j) (hL.mu0 j) (L.C.isMu0 j).tame m hunr x ⟨hinf, h1, h2⟩
    ⟨finPart D (((x : AE D) - 1) * incA D ((m : D.host.E)⁻¹)), (hΦ.int _).2 fun Q => ?_, ?_⟩
  · have e : Φ (((x : AE D) - 1) * incA D ((m : D.host.E)⁻¹)) Q =
        (Φ (x : AE D) Q - 1) * algebraMap D.host.E (Q.adicCompletion D.host.E) ((m : D.host.E)⁻¹) := by
      rw [ev_mul, hΦ.inc, map_sub, map_one]
      rfl
    rw [e]
    by_cases hQ : (m : 𝓞 D.host.E) ∈ Q.asIdeal
    · have hq : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
        rw [hmdef, Nat.cast_mul] at hQ
        rcases Q.isPrime.mem_or_mem hQ with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      obtain ⟨k, hk⟩ := hq
      have h1Q : Φ (x : AE D) Q = 1 := by
        rcases div_or_div_conj L.C.P k Q hk with h | h
        · exact (hx1 Q ((hL.Pg Q).2 ⟨k, h⟩)).1
        · have e2 : conjSpec Q = cP Q := (isConjPl_iff _ _).1 (isConjPl_conjSpec Q)
          rw [e2] at h
          have := (hx1 (cP Q) ((hL.Pg _).2 ⟨k, h⟩)).2
          rwa [cP_cP] at this
      rw [h1Q, sub_self, zero_mul]
      exact zero_mem _
    · refine mul_mem (sub_mem ((hΦ.int _).1 h1 Q) (one_mem _)) ?_
      have hm' : (m : 𝓞 D.host.E) ≠ 0 := fun h => hm0 (by exact_mod_cast congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h)
      have := (inv_mem_iff Q hm').2 hQ
      simpa using this
  · rw [nsmul_eq_mul, ← map_natCast (finPart D) m, ← map_mul, ← map_natCast (incA D) m, ← mul_assoc, mul_comm _ ((x : AE D) - 1),
      mul_assoc, ← map_mul, mul_inv_cancel₀ hm0, map_one, mul_one, map_sub, map_one]

end GlobalTheory.TypePlaceUnram
