import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.PropEG2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace Ad3P

def Lifts (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ) (π : TR.CuspSub ℚ 2) : Prop :=
  (∀ v, π.HasInfChar v (infOf ![0, 1 - (k : ℤ)])) ∧
  ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ B, π.HasSat w B ∧ ((algSat 2 (normV w) B).map fun b => X - C b).prod =
    X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))

def SEig : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ),
    Ad3.IsForm k N χ g.f g.a ∧ Ad3.IsEig k N χ g.a

def SPure : Prop :=
  UpperTheory.V.Af.HypothesesH → ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ g : Eigenform k N χ,
    Ad3.Pure k N χ g.a

def SCusp : Prop :=
  UpperTheory.V.Af.HypothesesH → ∀ (D : Ad3.Dat) (V : Submodule ℂ (Ad3.G3 → ℂ)) (hV : Ad3.WhA V), Ad3.Good D V hV →
    ∀ U : V →ₗ[ℂ] archSmooth ℚ 3,
    (∀ W : V, IsLeftInvariant (U W : Ad3.G3 → ℂ) ∧ HasModerateGrowth (U W : Ad3.G3 → ℂ) ∧ AutomorphicForm.IsCuspidal (U W : Ad3.G3 → ℂ) ∧
      FourierWhittaker.whittaker (U W : Ad3.G3 → ℂ) = W) →
    (∀ (W : V) h g, (U ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩ : Ad3.G3 → ℂ) g = (U W : Ad3.G3 → ℂ) (g * h)) →
    (∀ (W : V) i j, U ⟨_, hV.lie _ W.2 i j⟩ = Ad3.EA i j (U W)) →
    ∃ P : TR.CuspSub ℚ 3, (∀ v, P.HasInfChar v {(D.k : ℂ) - 1, 0, 1 - (D.k : ℂ)}) ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
        P.HasSat w {D.ν w (unifUnit (Ad3.Qv w)), 1, (D.ν w (unifUnit (Ad3.Qv w)))⁻¹}

def SDih : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (g : Eigenform k N χ) (π : TR.CuspSub ℚ 2),
    Lifts k N χ g π → Ad3.Dih g.a → ∃ η : HChar ℚ, η ≠ 1 ∧ η ^ 2 = 1 ∧ SelfTw π.HasSat η

def AdjEig : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (g : Eigenform k N χ) (π : TR.CuspSub ℚ 2),
    Lifts k N χ g π → (∃ η : HChar ℚ, η ≠ 1 ∧ η ^ 2 = 1 ∧ SelfTw π.HasSat η) ∨ ∃ P : TR.CuspSub ℚ 3,
      (∀ v (x y : ℂ), π.HasInfChar v {x, y} → P.HasInfChar v {x - y, 0, y - x}) ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ B, adSys π.HasSat w B ∧ P.HasSat w B

def SAdj : Prop := SEig → SPure → SCusp → SDih → Ad3.AdForm → UpperTheory.V.Af.HypothesesH → AdjEig

def PropEG' : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), UpperTheory.V.Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ (IrrOpen ρ → IsAutR ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹))

def SEG : Prop := UpperTheory.V.Af.HypothesesH → AdjEig → PropEG'

def SSeed : Prop := UpperTheory.V.Af.HypothesesH → PropEG' → Seed3

end Ad3P
