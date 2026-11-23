import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af
open CategoryTheory
open scoped Matrix
open UpperTheory.V.Published.Kato

namespace UpperTheory.V.Lit

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]

structure IsBKS (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation C (G F Ω) V) (c : G F Ω → V) : Prop where
  infl : ∀ s ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), c s = 0
  away : ∀ w ∈ S, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    ∃ x : V, ∀ s ∈ Ine (F := F) A, c s = ρ s x - x
  above : ∀ j : Ω →+* Formalism.BasicNotions.Loc.Om l, (fun x : ↥(decJ F j) => c x.1.1) ∈ Loc.finiteCocycles ((MonoidHom.snd _ _).comp (decJ F j).subtype)
    (ρ.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype))

def H1fSelmerVanishing (ρ : Representation C (G F Ω) V) : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → (∀ s ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ρ s = 1) →
    ∀ c ∈ Z1 ρ, IsBKS l S ρ c → c ∈ ReciprocityTheory.Gal.B1 ρ

end

def ThorneLit : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (n : ℕ), 2 ≤ n →
    ∀ (π : CuspSub F n) (χ : HChar (maximalRealSubfield F)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
    ∀ (μ : G (maximalRealSubfield F) Ω →* (Qbar p)ˣ), IsLAdicCharOf ι χ μ →
    ∃ (E : IntermediateField ℚ_[p] (Qbar p)) (_ : FiniteDimensional ℚ_[p] ↥E) (r : G F Ω →* GL (Fin n) ↥E),
      Continuous r ∧ AttC ι (toBar r) π ∧ (IsIrr ((toBar r).comp (cycBar F Ω p).ker.subtype) →
      ∀ c : G (maximalRealSubfield F) Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) →
      ∃ (P : GL (Fin n) ↥E) (ν : G F Ω →* (↥E)ˣ)
        (ρ : Representation ↥E (G (maximalRealSubfield F) Ω) (Matrix (Fin n) (Fin n) ↥E)),
        (P : Matrix (Fin n) (Fin n) ↥E)ᵀ = P ∧
        (∀ s, (((ν s : (↥E)ˣ) : ↥E) : Qbar p) =
          ((cycBar F Ω p s ^ (1 - (n : ℤ)) * μ (s.restrictScalars (maximalRealSubfield F)) : (Qbar p)ˣ) : Qbar p)) ∧
        (∀ s s' : G F Ω, s'.restrictScalars (maximalRealSubfield F) = c * s.restrictScalars (maximalRealSubfield F) * c⁻¹ →
          (r s : Matrix (Fin n) (Fin n) ↥E)ᵀ * (P : Matrix (Fin n) (Fin n) ↥E) * (r s' : Matrix (Fin n) (Fin n) ↥E) =
            (ν s : ↥E) • (P : Matrix (Fin n) (Fin n) ↥E)) ∧
        (∀ (s : G F Ω) (Y : Matrix (Fin n) (Fin n) ↥E), ρ (s.restrictScalars (maximalRealSubfield F)) Y =
          (r s : Matrix (Fin n) (Fin n) ↥E) * Y * ((r s)⁻¹ : GL (Fin n) ↥E)) ∧
        (∀ Y : Matrix (Fin n) (Fin n) ↥E, ρ c Y = -((P⁻¹ : GL (Fin n) ↥E) * Yᵀ * (P : Matrix (Fin n) (Fin n) ↥E))) ∧
        H1fSelmerVanishing p ρ)

end UpperTheory.V.Lit
