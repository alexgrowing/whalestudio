import Mathlib

noncomputable section

namespace PI.UnimodularOrthogonalQ2

open NumberField

def OKpair (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) :
    Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K))))

def hP {p : ℕ} [Fact p.Prime] {κ : Type} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

def IsBasisOver {p : ℕ} [Fact p.Prime] (O : Set (ℂ_[p] × ℂ_[p])) {κ ι : Type} [Fintype ι]
    (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e, b e ∈ Y) ∧ ∀ y ∈ Y, ∃! a : ι → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ O) ∧ y = fun k => ∑ e, a e * b e k

def Stmt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → d.Prime → b0 ^ 2 = -(d : K) → p ≠ d → (p = 2 → d % 8 = 7) →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : Fin r → κ → ℂ_[p] × ℂ_[p]),
      IsBasisOver (OKpair K c p τ) Y b →
      (∀ a : Fin r → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ OKpair K c p τ) → (fun k => ∑ e, a e * b e k) ∈ Y) →
      (∀ i j, hP (b i) (b j) ∈ OKpair K c p τ) →
      (∃ G : Fin r → Fin r → ℂ_[p] × ℂ_[p], (∀ i j, G i j ∈ OKpair K c p τ) ∧
        ∀ i k, ∑ j, hP (b i) (b j) * G j k = if i = k then 1 else 0) →
      ∃ b' : Fin r → κ → ℂ_[p] × ℂ_[p], IsBasisOver (OKpair K c p τ) Y b' ∧
        ∀ i j, hP (b' i) (b' j) = if i = j then 1 else 0

end PI.UnimodularOrthogonalQ2
