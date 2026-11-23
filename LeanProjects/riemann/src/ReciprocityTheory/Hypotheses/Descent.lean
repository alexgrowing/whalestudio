import ReciprocityTheory.GaloisValuations.SymplecticRankFourModularity

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter

namespace ReciprocityTheory.Hyp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def resGal (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] : G L Ω →* G K Ω :=
  AlgEquiv.restrictScalarsHom K

def SolubleDescent (𝒮 : SpectrumFamily) : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)], IsCMField K → IsCMField L →
  ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (ρ : G K Ω →* GL (Fin n) (Qbar l)), Continuous ρ →
    ConjSelfDualOne ρ → Irred (ρ.comp (resGal K L Ω)) →
  ∀ (k : Fin n → ℤ) (ι : Qbar l →+* ℂ),
    (∃ π' : (𝒮 L n).Rep, (∀ τ, (𝒮 L n).wt π' τ = k) ∧
      FrobMatch (ρ.comp (resGal K L Ω)) ι ((𝒮 L n).hecke π')) →
    ∃ π : (𝒮 K n).Rep, (∀ τ, (𝒮 K n).wt π τ = k) ∧ FrobMatch ρ ι ((𝒮 K n).hecke π)

def SolubleDescentReal (𝒮 : SpectrumFamily) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] [Group.IsSolvable (F ≃ₐ[ℚ] F)], IsTotallyReal F →
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra F Ω] [IsScalarTower ℚ F Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (ρ : G ℚ Ω →* GL (Fin n) (Qbar l)) (ν : G ℚ Ω →* (Qbar l)ˣ),
    Continuous ρ → SymplecticWith ρ ν → (∀ c, IsComplexConj c → ν c = -1) →
    Irred (ρ.comp (resGal ℚ F Ω)) →
  ∀ (k : Fin n → ℤ) (ι : Qbar l →+* ℂ), StrictAnti k →
    (∃ π' : (𝒮 F n).Rep, (∀ τ, (𝒮 F n).wt π' τ = k) ∧
      FrobMatch (ρ.comp (resGal ℚ F Ω)) ι ((𝒮 F n).hecke π')) →
    ∃ π : (𝒮 ℚ n).Rep, (∀ τ, (𝒮 ℚ n).wt π τ = k) ∧ FrobMatch ρ ι ((𝒮 ℚ n).hecke π)

def SolubleDescentCMReal (𝒮 : SpectrumFamily) : Prop :=
  ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L]
    [Group.IsSolvable (L ≃ₐ[F] L)], IsTotallyReal F → IsCMField L →
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra F Ω] [Algebra L Ω] [IsScalarTower ℚ F Ω]
    [IsScalarTower ℚ L Ω] [IsScalarTower F L Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (ρ : G ℚ Ω →* GL (Fin n) (Qbar l)) (ν : G ℚ Ω →* (Qbar l)ˣ),
    Continuous ρ → SymplecticWith ρ ν → (∀ c, IsComplexConj c → ν c = -1) →
    Irred (ρ.comp (resGal ℚ L Ω)) →
  ∀ (k : Fin n → ℤ) (ι : Qbar l →+* ℂ), StrictAnti k →
    (∃ π' : (𝒮 L n).Rep, (∀ τ, (𝒮 L n).wt π' τ = k) ∧
      FrobMatch (ρ.comp (resGal ℚ L Ω)) ι ((𝒮 L n).hecke π')) →
    ∃ π : (𝒮 F n).Rep, (∀ τ, (𝒮 F n).wt π τ = k) ∧
      FrobMatch (ρ.comp (resGal ℚ F Ω)) ι ((𝒮 F n).hecke π)

end ReciprocityTheory.Hyp
