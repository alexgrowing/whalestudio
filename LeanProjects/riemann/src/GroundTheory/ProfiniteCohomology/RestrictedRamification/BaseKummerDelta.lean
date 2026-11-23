import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
import GroundTheory.ProfiniteCohomology.PoincarePairs.Natural
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

theorem pow_notMem_asIdeal_of_forall (ℓ k : ℕ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    ∀ v ∉ S, (((ℓ ^ k : ℕ) : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv h => by
  rw [Nat.cast_pow] at h
  exact hv (hS v (v.isPrime.mem_of_pow_mem k h))

variable (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

include hnS in

theorem nsmul_gsRootsCompact (m : ℕ) (w : gsRootsCompact S ιs n m) : n • w = 0 := by
  obtain ⟨w', rfl⟩ := (bijective_gsRootsComparison S ιs n hnS m).2 w
  rw [← map_nsmul, nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S n) m w', map_zero]

abbrev gsRootsToUnitsCompact (m : ℕ) : gsRootsCompact S ιs n m ⟶ gsUnitsCompact S ιs m :=
  compactCohomologyMap (gsFinFamily S ιs) (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) m

theorem surjective_gsKummerCompactδ (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd ℓ ∨ IsTotallyComplex K.1) :
    Function.Surjective (gsKummerCompactδ S ιs n hnS 1).hom := by
  intro w
  have h0 : (gsRootsToUnitsCompact S ιs n (1 + 1)).hom w = 0 := by
    refine eq_zero_of_gsUnitsCompact_two S ιs ℓ hℓ hS hodd _ k ?_
    rw [← hnk, ← map_nsmul, nsmul_gsRootsCompact S ιs n hnS, map_zero]
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact₁ (gsFinFamily S ιs) (gsKummerLocalMap S ιs n) (gsKummer_shortExact S n hnS)
      (localKummer_shortExact S n) 1) h0

theorem gsKummerCompactδ_eq_zero_iff (h : gsUnitsCompact S ιs 1) :
    (gsKummerCompactδ S ιs n hnS 1).hom h = 0 ↔ ∃ h', h = n • h' := by
  constructor
  · intro hh
    obtain ⟨h', hh'⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
      (compactCohomology_exact₃ (gsFinFamily S ιs) (gsKummerLocalMap S ιs n) (gsKummer_shortExact S n hnS)
        (localKummer_shortExact S n) 1) hh
    refine ⟨h', hh'.symm.trans ?_⟩
    exact DFunLike.congr_fun (congrArg (fun F => F.hom) (compactCohomologyMap_nsmul_id (gsFinFamily S ιs)
      (a := gsSUnitsLocalMor S ιs) n (fun v => (gsKummerLocalMap S ιs n v).comm₂₃) 1)) h'
  · rintro ⟨h', rfl⟩
    rw [map_nsmul, nsmul_gsRootsCompact S ιs n hnS]

end

end GroundTheory.ProfCoh
