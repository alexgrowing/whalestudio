import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Z.Win.Birth

def PR {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : TR.CuspSub F n, π.IsRegAlg ∧ AttR ι r π ∧ PlainR π

def PrOrd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (ξ : G F Ω →* (Qbar l)ˣ) s c m a (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), OrdForm ι ξ s c m a π r → PR ι r

def PrTw : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) (κ : G F Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι κ → PR ι r → PR ι (tw r κ)

def PrIso : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → PR ι r → PR ι r'

def PropEGP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ PR ι ρ

def MixSeedP : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    Even (Module.finrank ℚ F) → SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ), IsOpen (ξ.ker : Set (G F Ω)) →
    (∀ c, IsConjEl c → ξ c = -1) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ ξ.ker) →
    (∃ (u : Pl F) (A : ValuationSubring Ω), normV u = 2 ∧ IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ ξ.ker) → (∃ g, ¬ Cong (ξ g ^ 2) 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    ∀ P : Set (Pl F), (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) → (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) →
    ∃ (k t : ℕ) (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), 2 ≤ k ∧ 2 ≤ t ∧ l - 1 ∣ k ∧ l - 1 ∣ t ∧
      Continuous r ∧ IrrOpen r ∧ AttR ι r π ∧ Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ k * ξ ∧ ResSum r ![1, ξ] ∧
      (TypeAway r ![1, ξ] ∧ PR ι r) ∧ ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal →
        (w ∈ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ) + t, -(t : ℤ)] ![ξ, 1] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ) + t, -(t : ℤ)])) ∧
        (w ∉ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ), 0] ![1, ξ] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ), 0]))

def MixOfP : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ),
    Hyp T k₀ φ → CharDat T k₀ φ → ∃ k t r, MixDat k₀ ι (up D.ξ) k t r ∧ PR ι r

def RhoExP : Prop :=
  PropEGP → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D),
    Ctx3 D → T₀.Ok → Four T₀ → ∀ (ι : Qbar l ≃+* ℂ) (B : ℕ) (c₀ : Coef l),
    ∃ (w : ℕ) (θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (c₁ : Coef l) (h : c.O ≤ c₁.O)
      (ρ₁ : G ℚ Ω →* M2 c₁.O) (x : ValuationSubring Ω → c₁.O), w.Prime ∧ T₀.Splits w ∧ θ ^ l = 1 ∧ KillsMu w θ ∧ B ≤ k ∧
      k - 1 ≡ D.e [MOD l - 1] ∧ EisRep ι (toB (phi D T₀.pr)) θ k ρ ∧ (IrrOpen ρ ∧ PR ι ρ) ∧ c₀.O ≤ c₁.O ∧
      Mod4 D T₀.pr θ k (resQ T₀.F T₀.g0) ρ h ρ₁ x

end UpperTheory.V.Z.Win.Birth
