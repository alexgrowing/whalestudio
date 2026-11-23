import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

def ExistsSplittingAuxiliaryCharacterForTower : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D), Ctx3 D →
    Four T₀ → ∃ (N w : ℕ) (θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ ∧ SplitAt N w (toB (phi D T₀.pr)) ∧ T₀.Splits w

def PhiFacts : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D), Ctx3 D →
    T₀.Ok → Four T₀ → phi D T₀.pr D.cc = -1 ∧ Even D.e ∧ ∀ k : ℕ, 1 ≤ k → k - 1 ≡ D.e [MOD l - 1] →
      Raw.bar (Phi D T₀.pr k) (resQ T₀.F T₀.g0) ^ 2 ≠ 1 ∧
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A, Raw.bar (Phi D T₀.pr k) s ≠ 1

def ModEx4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l) (D : Raw Ω c)
    (pr : Bool) (θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ), 1 ≤ k → ∀ ρ, EisRep ι (toB (phi D pr)) θ k ρ →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A, Raw.bar (Phi D pr k) s ≠ 1) →
    ∀ g0, Raw.bar (Phi D pr k) g0 ≠ 1 → ∀ c₀ : Coef l, ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (ρ₁ : G ℚ Ω →* M2 c₁.O)
      (x : ValuationSubring Ω → c₁.O), c₀.O ≤ c₁.O ∧ Mod4 D pr θ k g0 ρ h ρ₁ x

end UpperTheory.V.Cu2

end
