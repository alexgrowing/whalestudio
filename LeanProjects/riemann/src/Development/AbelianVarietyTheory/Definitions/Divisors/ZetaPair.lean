import Mathlib

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HenQ

def eulerL (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
    ((B w.1).map fun b => (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod

def eulerLd (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  eulerL K (fun w => (B w).map (·⁻¹)) S (1 - s)

def capPoly (m : Multiset ℂ) : ℂ[X] := (m.map fun z => (X + C z) * (X + C z + 1)).prod

def ZetaPair (L L' : ℂ → ℂ) (β : ℂ[X]) : Prop :=
  ∃ (Z W A B : ℂ → ℂ) (k : ℂ) (c : ℝ), Differentiable ℂ Z ∧ Differentiable ℂ W ∧ Z ≠ 0 ∧ W ≠ 0 ∧ k ≠ 0 ∧
    (∀ s : ℂ, c < s.re → Z s = L s * A s ∧ W s = L (s + 2) * β.eval s * A s) ∧
    (∀ s : ℂ, s.re < -c → Z s = L' s * B s ∧ W s = k * L' (s + 2) * B s)

end GlobalTheory.HenQ
