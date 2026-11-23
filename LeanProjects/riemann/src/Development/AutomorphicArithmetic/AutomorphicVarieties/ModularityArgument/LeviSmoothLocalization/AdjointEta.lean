import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

def RepOf (ι : Qbar l ≃+* ℂ) {k N : ℕ} {χ : DirichletCharacter ℂ N} (g : Eigenform k N χ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (∀ s ∈ Ine (F := ℚ) A, ρ s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV w) σ →
      (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom =
        X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))

def OfForm (ι : Qbar l ≃+* ℂ) (k : ℕ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ), χ.IsPrimitive ∧ ¬ l ∣ N ∧ RepOf ι g ρ

def PureAll : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ g : Eigenform k N χ, Ad3.Pure k N χ g.a

def PropEGF : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ 3 ≤ k ∧ OfForm ι k ρ ∧ (IrrOpen ρ → IsAutR ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹))

def PropEGFOf : Prop := Af.HypothesesH → Ad3P.AdjEig → PropEGF

def NotDih : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (k N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous ρ → IrrOpen ρ → RepOf ι g ρ →
    ¬ Ad3.Dih g.a

def AnEx : Prop :=
  PureAll → ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ g : Eigenform k N χ,
    Ad3.Dih g.a ∨ ∃ D : Ad3.Dat, D.k = k ∧ Ad3.SatOf N χ g.a D ∧ Ad3.An D

def AdSysOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (D : Ad3.Dat) (g : Eigenform D.k N χ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)), RepOf ι g ρ →
    Ad3.SatOf N χ g.a D → ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K Ω] (P : CuspSub K 3),
      AttC ι ((tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹).comp (galEmb ℚ K Ω)) P → AdSys D P

def AdWit : Prop :=
  PureAll → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (k : ℕ), 3 ≤ k →
    ∀ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IrrOpen ρ → OfForm ι k ρ →
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K Ω], Module.finrank ℚ K = 2 → ∀ P : CuspSub K 3,
      AttC ι ((tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹).comp (galEmb ℚ K Ω)) P → ∀ w, WinAt P 0 w

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
