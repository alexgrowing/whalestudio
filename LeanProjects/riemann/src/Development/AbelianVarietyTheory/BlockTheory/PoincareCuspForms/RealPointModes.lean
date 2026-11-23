import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealPointModes

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev Idx (E : Type) [Field E] [NumberField E] : Type :=
  Module.Free.ChooseBasisIndex ℤ (𝓞 (maximalRealSubfield E))

def modeAt (X : Data E r) (ν : maximalRealSubfield E) (τ : X.Ψ) : ℝ := (τ.1 (ν : E)).re

def modeTrace (X : Data E r) (ν : maximalRealSubfield E) : ℝ := ∑ τ, modeAt X ν τ

def realPoint (X : Data E r) (u : Idx E → ℝ) (τ : X.Ψ) : ℝ :=
  ∑ i, u i * modeAt X (integralBasis (maximalRealSubfield E) i) τ

def cubeMean (X : Data E r) (ξ : Fin r → E) (ν : maximalRealSubfield E)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (N : ℕ) : ℂ :=
  ∫ u in Set.Icc (0 : Idx E → ℝ) 1,
    P (X.flow ξ (fun τ => (((N : ℝ) * realPoint X u τ : ℝ) : ℂ)) x) *
      exp (-(4 * Real.pi * I) *
        ((∑ τ, modeAt X ν τ * ((N : ℝ) * realPoint X u τ) : ℝ) : ℂ))

def fj (X : Data E r) (ξ : Fin r → E) (ν : maximalRealSubfield E)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  Filter.limUnder Filter.atTop fun k : ℕ => cubeMean X ξ ν P x k.factorial

def IsIsotropic (X : Data E r) (ξ : Fin r → E) : Prop :=
  ξ ∈ X.Λ ∧ ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0

def IsShort (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1

def qq (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (τ : X.Ψ) : ℝ :=
  1 + (s τ).im / X.tt ξ x τ

def GrowthLE (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ) : Prop :=
  ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A)

def Moderate (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∃ C A : ℝ, 0 ≤ A ∧ GrowthLE X la P C A

def Bounded (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C

def SS (X : Data E r) (la : Wt X.Ψ r) : Set (Frame X.Ψ r → ℂ) :=
  {P | X.IsSec la P ∧ Bounded X la P ∧
    ∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, fj X ξ 0 P x = 0}

def SSgt (X : Data E r) (la : Wt X.Ψ r) (c : ℝ) : Set (Frame X.Ψ r → ℂ) :=
  {P | P ∈ SS X la ∧ ∀ ξ, IsIsotropic X ξ → ∀ ν : maximalRealSubfield E, modeTrace X ν ≤ c →
    ∀ x ∈ X.dom, fj X ξ ν P x = 0}

def FirstMinimumAlongFlow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (R : ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, IsShort X ξ x →
      ∀ s : X.Ψ → ℂ, (∀ τ, |(s τ).re| ≤ R) → (∀ τ, 0 < qq X ξ x s τ) →
        C⁻¹ * X.la1 x * (⨅ τ : X.Ψ, Real.sqrt (min (qq X ξ x s τ) (qq X ξ x s τ)⁻¹)) ≤
          X.la1 (X.flow ξ s x)

def CoefficientBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ), X.IsSec la P → 0 ≤ A → GrowthLE X la P C A →
    (∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, ∀ ν : maximalRealSubfield E,
      fj X ξ ν P x ≠ 0 → ∀ τ, 0 ≤ modeAt X ν τ) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ Cη : ℝ, ∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, IsShort X ξ x →
      ∀ ν : maximalRealSubfield E,
        X.pnorm la (fj X ξ ν P) x ≤ Cη * X.la1 x ^ (-A) *
          Real.exp (-(4 * Real.pi * (1 - η)) * ∑ τ, modeAt X ν τ * X.tt ξ x τ)

def ModesAdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la la' : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ),
    X.IsSec la P → Moderate X la P → X.IsSec la' Q → Moderate X la' Q →
    ∀ ξ, IsIsotropic X ξ → ∀ x ∈ X.dom, ∀ ν : maximalRealSubfield E,
      fj X ξ ν (P * Q) x ≠ 0 →
        ∃ ν₁ ν₂ : maximalRealSubfield E, ν₁ + ν₂ = ν ∧ fj X ξ ν₁ P x ≠ 0 ∧ fj X ξ ν₂ Q x ≠ 0

def CuspSpacesClosed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ la : Wt X.Ψ r, ∃ S : Submodule ℂ (Frame X.Ψ r → ℂ), (S : Set (Frame X.Ψ r → ℂ)) = SS X la) ∧
    (∀ (la : Wt X.Ψ r) (c : ℝ),
      ∃ S : Submodule ℂ (Frame X.Ψ r → ℂ), (S : Set (Frame X.Ψ r → ℂ)) = SSgt X la c) ∧
    (∀ (la la' : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ), P ∈ SS X la → X.IsSec la' Q → Bounded X la' Q →
      P * Q ∈ SS X (la + la')) ∧
    ∀ (la la' : Wt X.Ψ r) (c : ℝ) (P Q : Frame X.Ψ r → ℂ), P ∈ SSgt X la c → X.IsSec la' Q →
      Bounded X la' Q → P * Q ∈ SSgt X (la + la') c

def Statement : Prop :=
  FirstMinimumAlongFlow ∧ CoefficientBounds ∧ ModesAdd ∧ CuspSpacesClosed

end

end GlobalTheory.IndefiniteRowSideFullHecke.RealPointModes
