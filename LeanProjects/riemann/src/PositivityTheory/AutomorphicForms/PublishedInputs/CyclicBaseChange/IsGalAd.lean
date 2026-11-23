import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC

inductive Cusp (F : Type) [Field F] [NumberField F] (n : ℕ) : Type
  | cx [IsTotallyComplex F] (π : CuspSub F n)
  | re [IsTotallyReal F] (π : UpperTheory.V.TR.CuspSub F n)

namespace Cusp

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def sat : Cusp F n → HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop
  | cx π => (CG.mk π).HasSat
  | re π => π.HasSat

def inf : Cusp F n → (F →+* ℂ) → Multiset ℂ → Prop
  | cx π => π.HasInfChar
  | re π => fun τ => π.HasInfChar (InfinitePlace.mk τ)

def space : Cusp F n → Set (GA F n → ℂ)
  | cx π => {f | ∃ φ ∈ π.V, f = φ.1}
  | re π => {f | ∃ φ ∈ π.V, f = φ.1}

def Iso : Cusp F n → Cusp F n → Prop
  | cx π, cx π' => π.Iso π'
  | re π, re π' => π.Iso π'
  | _, _ => False

def twist : Cusp F n → HChar F → Cusp F n
  | cx π, η => cx (π.twist η)
  | re π, η => re (π.twist η)

end Cusp

variable {M : Type} [Field M] [NumberField M]

def IsGalAd (σ : M ≃+* M) (s : Ad M ≃+* Ad M) : Prop :=
  Continuous s ∧ (∀ x : M, s (algebraMap M (Ad M) x) = algebraMap M (Ad M) (σ x)) ∧ ∀ x, (s x).2 = conjFin σ x.2

def Cusp.ConjIso {n : ℕ} (P : Cusp M n) (σ : M ≃+* M) : Prop :=
  ∀ s : Ad M ≃+* Ad M, IsGalAd σ s → ∃ P' : Cusp M n,
    P'.space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' P.space ∧ P'.Iso P

def LitCBC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → (IsTotallyReal K ∨ IsTotallyComplex K) → (IsTotallyReal M ∨ IsTotallyComplex M) →
    ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ ∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧
      (∀ P : Cusp M n, (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ ∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        (∀ η : HChar K, IsNormChar M η → ¬ (π.twist η).Iso π) ∧
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

end UpperTheory.CBC
