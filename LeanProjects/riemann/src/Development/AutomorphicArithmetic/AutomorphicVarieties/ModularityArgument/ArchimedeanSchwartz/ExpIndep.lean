import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ

namespace UpperTheory.V.Z.Inf

def IsExp (f : ℂ → ℂ) : Prop := ∃ (T : Finset ℝ) (a : ℝ → ℂ), ∀ s, f s = ∑ t ∈ T, a t * Complex.exp (t * s)

def linPoly (m : Multiset ℂ) : ℂ[X] := (m.map fun z => X + C z).prod

def Pair (L L' : ℂ → ℂ) (β : ℂ[X]) : Prop :=
  ∃ (Z W A B T N D : ℂ → ℂ) (k k' : ℂ) (c : ℝ), Differentiable ℂ Z ∧ Differentiable ℂ W ∧ Z ≠ 0 ∧ k ≠ 0 ∧ k' ≠ 0 ∧
    IsExp N ∧ IsExp D ∧ D ≠ 0 ∧
    (∀ s : ℂ, c < s.re → Z s = L s * A s ∧ W s = k * L (s + 1) * β.eval s * A s) ∧
    ∀ s : ℂ, s.re < -c → T s * D s = N s ∧ T (s + 1) * D (s + 1) = N (s + 1) ∧
      Z s = L' s * B s * T s ∧ W s = k' * L' (s + 1) * B s * T (s + 1)

def cx {P : Type} (B : P → Multiset ℂˣ) (w : P) : Multiset ℂ := (B w).map fun b : ℂˣ => (b : ℂ)

def ExpAlg : Prop :=
  (∀ f, IsExp f → Differentiable ℂ f) ∧ (∀ f g, IsExp f → IsExp g → IsExp fun s => f s * g s) ∧
    (∀ c : ℂ, IsExp fun _ => c) ∧ (∀ f (z : ℂ), IsExp f → IsExp fun s => f (s + z)) ∧
    ∀ (p : ℂ[X]) (t : ℝ) (z : ℂ), IsExp fun s => p.eval (Complex.exp (t * (s + z)))

def ExpIndep : Prop :=
  ∀ (p q : ℂ[X]) (U V : ℂ → ℂ), IsExp U → IsExp V → U ≠ 0 → (∀ s, p.eval s * U s = q.eval s * V s) →
    ∃ u v : ℂ, u ≠ 0 ∧ C u * p = C v * q

def Cross : Prop := ∀ (L L' : ℂ → ℂ) (M N : Multiset ℂ), Pair L L' (linPoly M) → Pair L L' (linPoly N) → M = N

def PairOps : Prop :=
  (∀ (L L' L₁ L₁' : ℂ → ℂ) (β : ℂ[X]) (c : ℝ), Pair L L' β → (∀ s : ℂ, c < s.re → L s = L₁ s) →
    (∀ s : ℂ, s.re < -c → L' s = L₁' s) → Pair L₁ L₁' β) ∧
  ∀ (L L' : ℂ → ℂ) (m : Multiset ℂ) (z : ℂ), Pair L L' (linPoly m) →
    Pair (fun s => L (s - z)) (fun s => L' (s - z)) (linPoly (m.map (· - z)))

def Sep : Prop :=
  ∀ (I : Type) [Fintype I] (e : I → ℂ), Function.Injective e → ∀ A B : I → Multiset ℂ,
    (∀ k : ℕ, ∑ i, (A i).map (· + k * e i) = ∑ i, (B i).map (· + k * e i)) → A = B

def Regroup : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank K M = 2 →
    ∀ (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SM : Set (HeightOneSpectrum (𝓞 M))) (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
      (BM : HeightOneSpectrum (𝓞 M) → Multiset ℂ) (c₀ : ℝ) (r : ℕ), (∀ w, w ∈ SM ↔ w.under (𝓞 K) ∈ MainNotions) →
    (∀ p ∉ MainNotions, Multiset.card (BK p) ≤ r ∧ ∀ b ∈ BK p,
      ‖b‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀ ∧ ‖b⁻¹‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀) →
    (∀ w ∉ SM, Multiset.card (BM w) ≤ r ∧ ∀ b ∈ BM w,
      ‖b‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ∧ ‖b⁻¹‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀) →
    (∀ w ∉ SM, (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ∧ ∃ w', w' ≠ w ∧
        w'.under (𝓞 K) = w.under (𝓞 K) ∧ BK (w.under (𝓞 K)) = BM w + BM w') ∨
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 ∧ ∃ B' : Multiset ℂ,
        BM w = B'.map (· ^ 2) ∧ BK (w.under (𝓞 K)) = B' + B'.map Neg.neg)) →
    ∃ c : ℝ, ∀ s : ℂ, (c < s.re → eulerL K BK MainNotions s = eulerL M BM SM s) ∧ (s.re < -c → eulerLd K BK MainNotions s = eulerLd M BM SM s)

def CrossOf : Prop := ExpAlg → ExpIndep → Cross

end UpperTheory.V.Z.Inf
