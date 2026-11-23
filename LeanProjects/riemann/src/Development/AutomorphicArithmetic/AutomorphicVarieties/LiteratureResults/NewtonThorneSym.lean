import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lit

def NewtonThorneSym : Prop :=
  ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → (∀ χ : HChar ℚ, χ ≠ 1 → ¬ π.Iso (π.twist χ)) → ∀ n : ℕ, 1 ≤ n →
    ∃ P : TR.CuspSub ℚ (n + 1), P.IsRegAlg ∧
      ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (w : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion ℚ) → WD h), IsRec h rc →
        ∀ (σ : SmIrr (GL (Fin 2) (w.adicCompletion ℚ))) (τ : SmIrr (GL (Fin (n + 1)) (w.adicCompletion ℚ))),
          π.IsLocComp w σ → P.IsLocComp w τ →
          ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).mono0 → (rc (IrrGL.of τ.ρ τ.smooth τ.irred)).mono0) ∧
          ∀ (s : Weil h) (a b : ℂ), (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol s = (X - C a) * (X - C b) →
            (rc (IrrGL.of τ.ρ τ.smooth τ.irred)).charPol s = ∏ i ∈ Finset.range (n + 1), (X - C (a ^ (n - i) * b ^ i))

def NonCM : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (π : TR.CuspSub ℚ 2), Continuous ρ → AttR ι ρ π → IrrOpen ρ → ∀ χ : HChar ℚ, χ ≠ 1 → ¬ π.Iso (π.twist χ)

def SymSat : Prop :=
  ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → (∀ χ : HChar ℚ, χ ≠ 1 → ¬ π.Iso (π.twist χ)) → ∀ n : ℕ, 1 ≤ n →
    ∃ P : TR.CuspSub ℚ (n + 1), P.IsRegAlg ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      P.HasSat w ((Finset.range (n + 1)).val.map fun i => α ^ (n - i) * β ^ i)

def AdAutQ : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IsAutR ι ρ → IrrOpen ρ → IsAutR ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹)

def SymmetricCubeAutomorphyOverRationals : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IsAutR ι ρ → IrrOpen ρ → IsIrr (sym3 ρ) → IsAutR ι (sym3 ρ)

end UpperTheory.V.Lit
