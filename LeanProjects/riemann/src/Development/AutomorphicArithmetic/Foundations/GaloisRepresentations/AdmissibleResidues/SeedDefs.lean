import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RW
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.EndoscopicGroupCriteria.UnitaryUp3OfUpAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

namespace UpperTheory.GalN.V

def PropEGN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ

def PropEGuN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ ∧ Unlinked (ad0 ρ)

def PropEGadN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ ∧ Unlinked (ad0 ρ) ∧ (IrrOpen ρ → IsAutR ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹))

def MixedAdmissibleResidueMembership : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    Even (Module.finrank ℚ F) → SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ), IsOpen (ξ.ker : Set (G F Ω)) →
    (∀ c, IsConjEl c → ξ c = -1) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ ξ.ker) →
    (∃ (u : Pl F) (A : ValuationSubring Ω), normV u = 2 ∧ IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ ξ.ker) → (∃ g, ¬ Cong (ξ g ^ 2) 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    ∀ P : Set (Pl F), (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) → (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) →
    ∃ (k t : ℕ) (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), 2 ≤ k ∧ 2 ≤ t ∧ l - 1 ∣ k ∧ l - 1 ∣ t ∧
      Continuous r ∧ IrrOpen r ∧ AttR ι r π ∧ Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ k * ξ ∧ ResSum r ![1, ξ] ∧
      (TypeAway r ![1, ξ] ∧ RW ι r) ∧ ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal →
        (w ∈ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ) + t, -(t : ℤ)] ![ξ, 1] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ) + t, -(t : ℤ)])) ∧
        (w ∉ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ), 0] ![1, ξ] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ), 0]))

def MixOfN : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ),
    Hyp T k₀ φ → CharDat T k₀ φ → ∃ k t r, MixDat k₀ ι (up D.ξ) k t r ∧ RW ι r

def IndAutLN : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ) (k t : ℕ)
    (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
    IndDat T k₀ φ ι k t r α β R δ → RW ι r → IsAutC ι (R.comp (resQ T.L))

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)

def Wts0 (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ v i, ∀ s ∈ U ⊓ Ine (F := T.F) (T.pl v),
    P.ψ v i s ^ 2 = ((cycBar T.F Ω l s ^ h i : (PadicAlgCl l)ˣ) : PadicAlgCl l)

def WtsN (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  Wts0 T h P ∧ (h 1 + 4 ≤ h 0 → haveI := T.nF; Unlinked P.r.toHomUnits)

variable {T} {h : Fin 4 → ℤ} {P : PD T.ι (G T.F Ω) (PadicAlgCl l)}

theorem mkWts (k : Wts0 T h P) (_ : h 1 + 4 ≤ h 0 → haveI := T.nF; Unlinked P.r.toHomUnits) : T.Wts h P := k
theorem mkWts4 (k : Wts0 T (fun i => 2 * D.wts4 i) P) : T.Wts (fun i => 2 * D.wts4 i) P :=
  mkWts k fun hb => absurd hb (by simp [Raw.wts4]; omega)
end

end UpperTheory.GalN.V
