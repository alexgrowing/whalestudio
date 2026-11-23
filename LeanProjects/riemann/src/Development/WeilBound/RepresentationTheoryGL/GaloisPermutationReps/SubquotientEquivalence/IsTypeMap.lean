import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

def Lab (K : Type) [Field K] (n : ℕ) : Set K[X] := {P | P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = n}

def ExactPer (q n : ℕ) (z : ℂ) : Prop := z ≠ 0 ∧ z ^ q ^ n = z ∧ ∀ d, 0 < d → d < n → z ^ q ^ d ≠ z

def IrrPair {V : Type} [AddCommGroup V] [Module ℂ V] (M G : Module.End ℂ V) : Prop :=
  Nontrivial V ∧ ∀ U : Submodule ℂ V, (∀ v ∈ U, M v ∈ U) → (∀ v ∈ U, G v ∈ U) → U = ⊥ ∨ U = ⊤

def FinCusp {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] {n : ℕ} (τ : Representation ℂ (GL (Fin n) K) W) : Prop :=
  ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad K e ≠ ⊥ →
    ∀ v : W, (∀ u ∈ unipRad K e, τ u v = v) → v = 0

def IsTypeMap {k W V : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (τ : Representation ℂ (GL (Fin n) 𝓀[k]) W) (π : Representation ℂ (GL (Fin n) k) V) (j : W →ₗ[ℂ] V) : Prop :=
  Function.Injective j ∧ ∀ (g : KO k (Fin n)) (v : W), j (τ (redK k (Fin n) g) v) = π (g : GL (Fin n) k) (j v)

def St1a : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (q : ℕ) (M G : Module.End ℂ V),
    IsUnit M → IsUnit G → M * G = G * M ^ q → IrrPair M G →
    ∃ z : ℂ, M.HasEigenvalue z ∧ ExactPer q (Module.finrank ℂ V) z

def St1b : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (q n i : ℕ) (M G : Module.End ℂ V) (M' G' : Module.End ℂ V') (z : ℂ),
    0 < n → Module.finrank ℂ V = n → Module.finrank ℂ V' = n → IsUnit G → IsUnit G' → M * G = G * M ^ q →
    M' * G' = G' * M' ^ q → ExactPer q n z → M.HasEigenvalue z → M'.HasEigenvalue (z ^ q ^ i) →
    LinearMap.det G = LinearMap.det G' →
    ∃ e : V ≃ₗ[ℂ] V', (∀ v, e (M v) = M' (e v)) ∧ ∀ v, e (G v) = G' (e v)

def St2 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (φ : Weil h), deg φ = -1 → ∃ γ : Weil h,
    (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)), (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) →
      a.ρ γ * a.ρ φ = a.ρ φ * a.ρ γ ^ normV w ∧ (a.ρ.IsIrreducible → IrrPair (a.ρ γ) (a.ρ φ))) ∧
    ∀ (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)),
      (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) →
      (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1) → a.ρ.IsIrreducible → b.ρ.IsIrreducible →
      ∀ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), (∀ v, e (a.ρ γ v) = b.ρ γ (e v)) → (∀ v, e (a.ρ φ v) = b.ρ φ (e v)) → a.Iso b

def St3a : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 0 < n → ∃ lab : ℂ → K[X],
    (∀ z, ExactPer (Nat.card K) n z → lab z ∈ Lab K n) ∧
    ∀ z z', ExactPer (Nat.card K) n z → ExactPer (Nat.card K) n z' → lab z = lab z' → ∃ i : ℕ, z' = z ^ Nat.card K ^ i

def TameSet {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (φ : Weil h) (n : ℕ) (c : ℂ) : Set (WD h) :=
  {y | IsIrrWD y ∧ IsTameWD y ∧ y.lpDim = n ∧ (y.eig φ).prod = c}

def St3 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (φ : Weil h), deg φ = -1 → ∀ (n : ℕ) (c : ℂ), 0 < n →
    ∃ f : WD h → (𝓀[w.adicCompletion E])[X],
      Set.MapsTo f (TameSet φ n c) (Lab 𝓀[w.adicCompletion E] n) ∧ Set.InjOn f (TameSet φ n c)

def St4 : Prop :=
  ∀ (k W : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (n : ℕ), 0 < n →
    ∀ τ : Representation ℂ (GL (Fin n) 𝓀[k]) W, τ.IsIrreducible → ∀ ϖ : kˣ, ord k ϖ = 1 → ∀ c : ℂˣ,
    ∃ (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (j : W →ₗ[ℂ] π.V),
      HasCentralChar π.ρ ω ∧ ω ϖ = c ∧ IsTypeMap τ π.ρ j

def St5 : Prop :=
  ∀ (k W : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W] (n : ℕ) (τ : Representation ℂ (GL (Fin n) 𝓀[k]) W), FinCusp τ →
    ∀ (π : IrrRep (GL (Fin n) k)) (j : W →ₗ[ℂ] π.V), IsTypeMap τ π.ρ j → IsCuspidal π.ρ

def St6 : Prop :=
  ∀ (k W : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W] (n : ℕ) (τ : Representation ℂ (GL (Fin n) 𝓀[k]) W), FinCusp τ →
    ∀ (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ), HasCentralChar π.ρ ω →
    ∀ j : W →ₗ[ℂ] π.V, IsTypeMap τ π.ρ j → fixed π.ρ (KOne k (Fin n)) = LinearMap.range j

def St7 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 0 < n → ∃ τ : K[X] → FDRep ℂ (GL (Fin n) K),
    (∀ P ∈ Lab K n, Representation.IsIrreducible (τ P).ρ ∧ FinCusp (τ P).ρ) ∧
    ∀ P ∈ Lab K n, ∀ P' ∈ Lab K n,
      (∃ e : τ P ≃ₗ[ℂ] τ P', ∀ g v, e ((τ P).ρ g v) = (τ P').ρ g (e v)) → P = P'

def Fwd : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
    ∀ x : IrrGL (w.adicCompletion E), x.IsCusp →
      fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x)

def St8a : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), 0 < n →
    ∀ ϖ : kˣ, ord k ϖ = 1 → ∀ c : ℂˣ, ∃ X : (𝓀[k])[X] → IrrGL k,
      (∀ P ∈ Lab 𝓀[k] n, (X P).1 = n ∧ (X P).IsCusp ∧ fixed (X P).rep (KOne k (Fin (X P).1)) ≠ ⊥ ∧
        ∃ ω : kˣ →* ℂˣ, HasCentralChar (X P).rep ω ∧ ω ϖ = c) ∧ Set.InjOn X (Lab 𝓀[k] n)

end PositivityTheory.Rg.DzCount

end
