import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section

namespace GlobalTheory.PrimeReach

theorem prime_contraction_or_dvr : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (p : PrimeSpectrum R₁), p ∈ Set.range (PrimeSpectrum.comap R₁.subtype) ∨ ∃ (Q : PrimeSpectrum R) (k : Type) (_ : Field k) (i : R₁ →+* k) (j : k →+* Q.asIdeal.ResidueField) (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ρ : R₁ →+* V) (e : k →+* FractionRing V), j.comp i = (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype ∧ e.comp i = (algebraMap V (FractionRing V)).comp ρ ∧ p ∈ Set.range (PrimeSpectrum.comap ρ) := by
  intro R _ R₁ _ p
  by_cases hp : p ∈ Set.range (PrimeSpectrum.comap R₁.subtype)
  · exact Or.inl hp
  right
  haveI := p.isPrime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R₁)) (J := p.asIdeal) bot_le
  obtain ⟨P, hP, hPq⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := R₁.subtype) Subtype.val_injective q hq
  let Q : PrimeSpectrum R := ⟨P, hP⟩
  haveI hqpr : q.IsPrime := hq.1.1
  let f₀ : R₁ →+* Q.asIdeal.ResidueField := (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype
  have hker : RingHom.ker f₀ = q := by
    rw [← hPq]
    ext x
    simp only [f₀, RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    exact (Ideal.algebraMap_residueField_eq_zero).trans Iff.rfl
  let A := R₁ ⧸ q
  let g₀ : A →+* Q.asIdeal.ResidueField := Ideal.Quotient.lift q f₀ (fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha)
  have hg₀ : Function.Injective g₀ := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker] at hx
    exact (Submodule.mem_bot _).2 (Ideal.Quotient.eq_zero_iff_mem.2 hx)
  let k := FractionRing A
  let i : R₁ →+* k := (algebraMap A k).comp (Ideal.Quotient.mk q)
  let j : k →+* Q.asIdeal.ResidueField := IsFractionRing.lift hg₀
  have hji : j.comp i = f₀ := by
    ext x
    simp only [i, j, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    rfl
  let p' : Ideal A := p.asIdeal.map (Ideal.Quotient.mk q)
  haveI hp' : p'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hqp)
  have hcp' : p'.comap (Ideal.Quotient.mk q) = p.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.2 hqp
  let O := Localization.AtPrime p'
  haveI : IsDomain O := IsLocalization.isDomain_localization p'.primeCompl_le_nonZeroDivisors
  have hOinj : Function.Injective (algebraMap A O) := IsLocalization.injective O p'.primeCompl_le_nonZeroDivisors
  have hcm : (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p' := Localization.AtPrime.comap_maximalIdeal
  have hnf : ¬ IsField O := by
    intro hF
    apply hp
    have hm : IsLocalRing.maximalIdeal O = ⊥ := by
      letI := hF.toField
      exact IsLocalRing.maximalIdeal_eq_bot
    have h1 : p' = ⊥ := by
      rw [← hcm, hm, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).1 hOinj]
    refine ⟨Q, PrimeSpectrum.ext ?_⟩
    show P.comap R₁.subtype = p.asIdeal
    rw [hPq, ← hcp', h1, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  obtain ⟨V, _, _, _, ρ₀, hρinj, hρloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hnf
  let ρ : R₁ →+* V := ρ₀.comp ((algebraMap A O).comp (Ideal.Quotient.mk q))
  let g' : A →+* FractionRing V := (algebraMap V (FractionRing V)).comp (ρ₀.comp (algebraMap A O))
  have hg' : Function.Injective g' := (IsFractionRing.injective V (FractionRing V)).comp (hρinj.comp hOinj)
  let e : k →+* FractionRing V := IsFractionRing.lift hg'
  refine ⟨Q, k, inferInstance, i, j, V, inferInstance, inferInstance, inferInstance, ρ, e, hji, ?_, ?_⟩
  · ext x
    simp only [e, i, ρ, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    rfl
  · have hmV : (IsLocalRing.maximalIdeal V).comap ρ₀ = IsLocalRing.maximalIdeal O := by
      refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal V).ne_top)) ?_
      intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal x).1 hx (isUnit_of_map_unit ρ₀ x hu)
    refine ⟨⟨IsLocalRing.maximalIdeal V, inferInstance⟩, PrimeSpectrum.ext ?_⟩
    show (IsLocalRing.maximalIdeal V).comap ρ = p.asIdeal
    rw [show ρ = (ρ₀.comp (algebraMap A O)).comp (Ideal.Quotient.mk q) from rfl, ← Ideal.comap_comap,
      ← Ideal.comap_comap, hmV, hcm, hcp']

end GlobalTheory.PrimeReach
