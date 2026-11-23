import Mathlib

namespace Formalism.SL.LF

open scoped NumberField
open NumberField InfinitePlace Finset

def ProdBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K) (H : ℝ), x ≠ 0 → 1 ≤ H →
    (∀ w : InfinitePlace K, w (x : K) ≤ H) →
    ∏ w : InfinitePlace K, (max 1 (w (x : K))⁻¹) ^ w.mult ≤ H ^ Module.finrank ℚ K

def ProdBoundFrac : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : K) (a : 𝓞 K) (H : ℝ), x ≠ 0 → a ≠ 0 → 1 ≤ H →
    (∃ y : 𝓞 K, (y : K) = (a : K) * x) →
    (∀ w : InfinitePlace K, w x ≤ H) →
    ∏ w : InfinitePlace K, (max 1 (w x)⁻¹) ^ w.mult
      ≤ H ^ Module.finrank ℚ K * |Algebra.norm ℚ (a : K)|

def ProdBoundIdeal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : K) (I : Ideal (𝓞 K)) (H : ℝ), x ≠ 0 → I ≠ ⊥ → 1 ≤ H →
    (∀ y ∈ I, ∃ z : 𝓞 K, (z : K) = (y : K) * x) →
    (∀ w : InfinitePlace K, w x ≤ H) →
    ∏ w : InfinitePlace K, (max 1 (w x)⁻¹) ^ w.mult ≤ H ^ Module.finrank ℚ K * (Ideal.absNorm I : ℝ)

def ProdInv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : 𝓞 K), D ≠ 0 →
    ∏ w : InfinitePlace K, (max 1 (w (D : K))⁻¹) ^ w.mult
      ≤ ∏ w : InfinitePlace K, (max 1 (w (D : K))) ^ w.mult

def ProdRatio : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : 𝓞 K), A ≠ 0 → B ≠ 0 →
    ∏ w : InfinitePlace K, (max 1 (w ((A : K) / (B : K)))) ^ w.mult
      ≤ ∏ w : InfinitePlace K, (max 1 (w (A : K)) * max 1 (w (B : K))) ^ w.mult

def BoxCount : Prop :=
  ∀ (f : ℕ) (S : Finset (Fin f → ℂ)) (y : Fin f → ℂ) (ρ : Fin f → ℝ),
    (∀ z ∈ S, ∀ v, ‖z v - y v‖ ≤ ρ v) →
    (∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → 1 ≤ ∏ v, ‖z v - z' v‖ ^ 2) →
    (S.card : ℝ) ≤ 16 ^ f * max 1 (∏ v, (2 * ρ v) ^ 2)

def BoxRing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], (∀ w : InfinitePlace K, w.IsComplex) →
    ∀ (y : InfinitePlace K → ℂ) (ρ : InfinitePlace K → ℝ),
      {x : 𝓞 K | ∀ w, ‖w.embedding (x : K) - y w‖ ≤ ρ w}.Finite ∧
      ({x : 𝓞 K | ∀ w, ‖w.embedding (x : K) - y w‖ ≤ ρ w}.ncard : ℝ)
        ≤ 16 ^ Fintype.card (InfinitePlace K) * max 1 (∏ w, (2 * ρ w) ^ 2)

def Sobolev1 : Prop :=
  ∀ (φ φ' : ℝ → ℂ) (a δ : ℝ), 0 < δ →
    (∀ t ∈ Set.Icc a (a + δ), HasDerivAt φ (φ' t) t) →
    ContinuousOn φ' (Set.Icc a (a + δ)) →
    ∀ x ∈ Set.Icc a (a + δ),
      ‖φ x‖ ^ 2 ≤ 2 / δ * ∫ t in a..(a + δ), (‖φ t‖ ^ 2 + δ ^ 2 * ‖φ' t‖ ^ 2)

def BinaryCode : Prop :=
  ∀ (k : ℕ) (v : Fin k → ℝ) (Δ : ℝ), 0 < Δ →
    Fintype.card (Fin k → Bool) = 2 ^ k ∧
    (∀ w w' : Fin k → Bool, w ≠ w' →
      (∃ i, |(v i - 1 / 2 - (if w i then Δ else 0)) - (v i - 1 / 2 - (if w' i then Δ else 0))| = Δ) ∧
      Δ ≤ ∑ i, |(v i - 1 / 2 - (if w i then Δ else 0)) - (v i - 1 / 2 - (if w' i then Δ else 0))|) ∧
    (∀ X : ℝ, Real.exp X ≤ 2 ^ k ↔ X ≤ k * Real.log 2)

def PrimesOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : ℕ), p.Prime →
    {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P}.Finite ∧
    {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P}.ncard ≤ Module.finrank ℚ K

end Formalism.SL.LF
