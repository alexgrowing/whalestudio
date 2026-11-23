import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

def Rp (K : Type) [Field K] [NumberField K] (p : ℕ) (x : K) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) * x ∈ (algebraMap (𝓞 K) K).range

def hf {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w : ι → K) : K :=
  ∑ i, v i * c (w i)

def IsUnitary {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    (u : (ι → K) ≃ₗ[K] (ι → K)) : Prop :=
  ∀ v w, hf c (u v) (u w) = hf c v w

def SplitK {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 K), P.IsPrime ∧ ((p : ℕ) : 𝓞 K) ∈ P ∧
    ∃ a b : 𝓞 K, c (a : K) = (b : K) ∧ a ∈ P ∧ b ∉ P

def Unimod (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type} [Fintype ι]
    (L : Set (ι → K)) : Prop :=
  ∀ v, v ∈ L ↔ ∀ w ∈ L, Rp K p (hf c v w)

def Spans (K : Type) [Field K] {ι : Type} (L : Set (ι → K)) : Prop :=
  ∀ v : ι → K, ∃ N : ℕ, N ≠ 0 ∧ (N : K) • v ∈ L

def NormOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
    (L : Set (ι → K)),
    Module.finrank ℚ K = 2 → (∀ x, c (c x) = x) → p.Prime → SplitK c p →
      Unimod K c p L → Spans K L → ∃ e ∈ L, hf c e e = 1

def LatIso : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) (ι : Type) [Fintype ι]
    (L : Set (ι → K)),
    Module.finrank ℚ K = 2 → (∀ x, c (c x) = x) → p.Prime → SplitK c p →
      Unimod K c p L → Spans K L →
        ∃ u : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c u ∧ ∀ v, v ∈ L ↔ ∀ i, Rp K p (u v i)

def LocalIsoOfLatticeIso : Prop := LatIso → PI.KerIso.LocIso

def LatticeFromNormOne : Prop := NormOne → LatIso

end PI.KLW
