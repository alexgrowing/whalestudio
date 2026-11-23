import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.CommAlg.OrderEtale

theorem formallyUnramified_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] [Field K] [Algebra k K] [IsFractionRing k K] [Algebra ℤ K] :
    Algebra.FormallyUnramified ℤ K := by
  have hinj : Function.Injective (algebraMap k K) := IsFractionRing.injective k K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K) (RingHom.ext_int _ _)
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := k) (A := K) (RingHom.ext_int _ _)
  haveI : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hint : ∀ a : k, IsIntegral ℚ (algebraMap k K a) := fun a =>
    IsIntegral.tower_top (A := ℚ)
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap (B := K))
  haveI : Algebra.IsAlgebraic ℚ K := by
    constructor
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := k) x
    rw [div_eq_mul_inv]
    have hb : IsIntegral ℚ (algebraMap k K b)⁻¹ :=
      (IsAlgebraic.inv_iff.mpr (hint b).isAlgebraic).isIntegral
    exact ((hint a).mul hb).isAlgebraic
  haveI : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  exact Algebra.FormallyUnramified.comp ℤ ℚ K

theorem isUnramifiedAt_bot (k : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] : Algebra.IsUnramifiedAt ℤ (⊥ : Ideal k) := by
  have hM : (⊥ : Ideal k).primeCompl = nonZeroDivisors k := by
    ext x
    simp [Ideal.mem_primeCompl_iff, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsFractionRing k (Localization.AtPrime (⊥ : Ideal k)) := by
    unfold IsFractionRing
    rw [← hM]
    infer_instance
  letI : Field (Localization.AtPrime (⊥ : Ideal k)) := IsFractionRing.toField k
  exact formallyUnramified_fractionRing k (Localization.AtPrime (⊥ : Ideal k))

theorem exists_etale_away (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ∃ N : ℕ, N ≠ 0 ∧ (Int.castRingHom (Localization.Away (N : k))).Etale := by
  have hU : IsOpen (Algebra.unramifiedLocus ℤ k) := Algebra.isOpen_unramifiedLocus
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) ∈ Algebra.unramifiedLocus ℤ k :=
    isUnramifiedAt_bot k
  obtain ⟨V, ⟨f, rfl⟩, hfV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hU
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hfV
  have hint : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hne : Ideal.comap (algebraMap ℤ k) (Ideal.span {f}) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.subset_span rfl) (Algebra.IsIntegral.isIntegral f)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, eq_intCast] at hm
  have hmN : (m : k) ∣ ((m.natAbs : ℤ) : k) := map_dvd (Int.castRingHom k) (Int.dvd_natAbs.mpr dvd_rfl)
  have hfN : f ∣ ((m.natAbs : ℕ) : k) := by
    have := hm.trans hmN
    simpa using this
  obtain ⟨g, hg⟩ := hfN
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr hm0, ?_⟩
  have hS : Algebra.FormallyUnramified ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    rw [← Algebra.basicOpen_subset_unramifiedLocus_iff]
    refine subset_trans ?_ hVU
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left f g
  have hfree : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  have hflat : Module.Flat ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have := IsLocalization.flat (Localization.Away ((m.natAbs : ℕ) : k))
      (Submonoid.powers ((m.natAbs : ℕ) : k))
    exact Module.Flat.trans ℤ k _
  have hfp : Algebra.FinitePresentation ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have : Algebra.FinitePresentation ℤ k := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have := IsLocalization.Away.finitePresentation (S := Localization.Away ((m.natAbs : ℕ) : k))
      ((m.natAbs : ℕ) : k)
    exact Algebra.FinitePresentation.trans ℤ k _
  have hE : Algebra.Etale ℤ (Localization.Away ((m.natAbs : ℕ) : k)) :=
    Algebra.Etale.of_formallyUnramified_of_flat
  have h2 : Int.castRingHom (Localization.Away ((m.natAbs : ℕ) : k)) =
      algebraMap ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := RingHom.ext_int _ _
  rw [h2, RingHom.etale_algebraMap]
  exact hE

end GlobalTheory.CompanionTheory.CommAlg.OrderEtale
