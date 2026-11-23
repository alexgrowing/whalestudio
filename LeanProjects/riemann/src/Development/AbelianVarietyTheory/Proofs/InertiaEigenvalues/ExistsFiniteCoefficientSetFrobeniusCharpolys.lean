import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinsetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.FrobSysCoef

theorem main : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ ρ₀ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l),
      Continuous (fun g => ((ρ₀ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep ρ₀ ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ)
  · obtain ⟨ρ₀, hc₀, hs₀, hp₀⟩ := hex
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.galoisRep_entries_mem_of_finset l E Ω a ρ₀ hc₀
    refine ⟨S₀.image ι, fun K hK ρ hc hs hp => ?_⟩
    have hK' : ∀ z ∈ S₀, z ∈ K := fun z hz => by
      simpa using hK (ι z) (Finset.mem_image_of_mem _ hz)
    have hU' : ∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
        ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := fun σ hσ =>
      Polynomial.map_injective ι.toRingHom ι.injective ((hp₀ σ hσ).trans (hp σ hσ).symm)
    have hall := GlobalTheory.charpoly_eq_of_eqOn_dense _ _ hc₀ hc U hU hU'
    obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₀ ρ hs₀ hs hall
    refine ⟨Pm⁻¹, fun g s t => ?_⟩
    have : Pm⁻¹⁻¹ * ρ g * Pm⁻¹ = ρ₀ g := by
      rw [hPm g, inv_inv]; group
    rw [this]
    exact hS₀ K hK' g s t
  · refine ⟨∅, fun K _ ρ hc hs hp => ?_⟩
    exact absurd ⟨ρ, hc, hs, hp⟩ hex

end GlobalTheory.FrobSysCoef
