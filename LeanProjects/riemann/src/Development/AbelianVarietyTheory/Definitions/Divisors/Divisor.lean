import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Vanishing

namespace GlobalTheory.CuspDim

variable {k : Type} [CommRing k] {Z : Scheme.{0}}

section Growth

variable (p : Z ⟶ Sp k) (σ : k →+* ℂ) (O : Z.Opens)

def push : CxPts (O.ι ≫ p) σ → CxPts p σ := PtsOver.map O.ι rfl _

variable {p σ}

structure NcChart {D : ℕ} (y : CxPts p σ) (e : OpenPartialHomeomorph (CxPts p σ) (V D)) (S : Finset (Fin D)) : Prop where

  holo : ∀ (W : Z.Opens) (f : Γ(Z, W)), DifferentiableOn ℂ (ev p σ W f ∘ e.symm) (e.target ∩ e.symm ⁻¹' ptsIn p σ W)

  mem : y ∈ e.source

  centre : ∀ a ∈ S, e y a = 0

  bd : ∀ z ∈ e.source, z ∉ ptsIn p σ O ↔ ∃ a ∈ S, e z a = 0

def LogAt (D : ℕ) (φ : CxPts (O.ι ≫ p) σ → ℝ) (y : CxPts p σ) : Prop :=
  ∃ (e : OpenPartialHomeomorph (CxPts p σ) (V D)) (S : Finset (Fin D)), NcChart O y e S ∧ ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ᶠ z in comap (push p σ O) (𝓝 y), φ z ≤ C * (1 + ∑ a ∈ S, |Real.log ‖e (push p σ O z) a‖|) ^ N

def LogEq (W : Z.Opens) (b : Γ(Z, W)) (φ : CxPts (O.ι ≫ p) σ → ℝ) (y : CxPts p σ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ᶠ z in comap (push p σ O) (𝓝 y), φ z ≤ C * (1 + |Real.log ‖ev p σ W b (push p σ O z)‖|) ^ N

end Growth

section Metric

variable {q : Z ⟶ Sp k} {σ : k →+* ℂ} {A B : LB Z}

def IsoM (φ : Weight q σ A) (ψ : Weight q σ B) : Prop :=
  ∃ w : LB.Iso A B, w.IsGen ∧ ∀ (a : A.ι) (b : B.ι) (y : CxPts q σ), y ∈ ptsIn q σ (A.U a) → y ∈ ptsIn q σ (B.U b) →
    ψ.φ b y = φ.φ a y + Real.log (‖ev q σ _ (w.s (b, a)).val y‖ ^ 2)

def len (φ : Weight q σ B) (s : H0 q B ⊤) (y : CxPts q σ) : ℝ := φ.nsq (secVal q σ (GlobalTheory.CompHS.toSec s)) y

def Scales (φ : Weight q σ A) (ψ : Weight q σ B) (G : H0 q A ⊤ →ₗ[k] H0 q B ⊤) (c : CxPts q σ → ℝ) : Prop :=
  Function.Injective G ∧ ∀ s y, len ψ (G s) y = c y * len φ s y

end Metric

structure HidaSetting {k : Type} [Field k] (σ : k →+* ℂ) {Z : Scheme.{0}} (p : Z ⟶ Sp k) (D : ℕ) (Λ : Type) [AddCommGroup Λ] where

  smooth : SmoothOfRelativeDimension D p

  proj : IsProjOver p

  integral : IsIntegral Z

  O : Z.Opens

  divisor : ∀ x ∉ O, ∃ (W : Z.Opens) (b : Γ(Z, W)), IsAffineOpen W ∧ x ∈ W ∧ Z.basicOpen b = W ⊓ O

  nc : ∀ y ∉ ptsIn p σ O, ∃ (e : OpenPartialHomeomorph (CxPts p σ) (V D)) (S : Finset (Fin D)), NcChart O y e S

  ℒ : Λ → LB O.toScheme

  h : ∀ w, Weight (O.ι ≫ p) σ (ℒ w)

  mul : ∀ w w', IsoM ((h w).tens (h w')) (h (w + w'))

  u' : Λ

  u₁ : Λ

  S : ∀ n : ℕ, Submodule k (H0 (O.ι ≫ p) (ℒ (n • u')) ⊤)

  bdd : ∀ n, 1 ≤ n → ∀ f ∈ S n, ∃ C : ℝ, ∀ z, len (h (n • u')) f z ≤ C

  τ : H0 (O.ι ≫ p) (ℒ (u₁ - u')) ⊤

  τ_ne : τ ≠ 0

  τ_log : ∀ y ∉ ptsIn p σ O, LogAt O D (len (h (u₁ - u')) τ) y

  L : LB Z

  isLB : L.IsLB

  hL : Weight (O.ι ≫ p) σ (L.pull O.ι)

  ext : IsoM (h (3 • u₁ - 2 • u')) hL

  good : ∀ y ∉ ptsIn p σ O, ∀ i, y ∈ ptsIn p σ (L.U i) →
    LogAt O D (fun z => Real.exp (-hL.φ (fun _ => i) z)) y ∧ LogAt O D (fun z => Real.exp (hL.φ (fun _ => i) z)) y

end GlobalTheory.CuspDim
