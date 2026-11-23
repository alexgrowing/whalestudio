import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published

def ChebotarevOpenNormal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → U.Normal →
    ∀ (g : G F Ω) (A : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ v : HeightOneSpectrum (𝓞 F), v ∉ A ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧
        ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Ine (F := F) B ≤ U ∧
          ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ σ * g⁻¹ ∈ U

theorem chebotarevOpenNormal_iff_cheb : ChebotarevOpenNormal ↔ GlobalTheory.TwSys.Cheb := Iff.rfl

theorem chebotarevOpenNormal_iff_degreeOne : ChebotarevOpenNormal ↔ ChebotarevDegreeOne :=
  chebotarevDegreeOne_iff_cheb.symm

theorem chebotarevOpenNormal_iff_infinite : ChebotarevOpenNormal ↔
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → U.Normal → ∀ g : G F Ω,
      {v : HeightOneSpectrum (𝓞 F) | (Ideal.absNorm v.asIdeal).Prime ∧
        ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Ine (F := F) B ≤ U ∧
          ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ σ * g⁻¹ ∈ U}.Infinite := by
  classical
  constructor
  · intro h F Ω _ _ _ _ _ U hU hN g hfin
    obtain ⟨v, hv, hd, -, hB⟩ := h F Ω U hU hN g hfin.toFinset
    exact hv (hfin.mem_toFinset.2
      ⟨((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd, hB⟩)
  · intro h F Ω _ _ _ _ _ U hU hN g A
    have hfin := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).2
    obtain ⟨v, ⟨hp, hB⟩, hv⟩ := ((h F Ω U hU hN g).sdiff (A.finite_toSet.union hfin)).nonempty
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
    exact ⟨v, hv.1, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).1 hp,
      by simpa using hv.2, hB⟩

end GlobalTheory.Published

end
