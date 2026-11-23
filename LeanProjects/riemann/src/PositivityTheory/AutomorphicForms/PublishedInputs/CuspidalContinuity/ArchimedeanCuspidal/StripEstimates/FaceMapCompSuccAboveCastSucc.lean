import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped MatrixGroups ModularForm Modular ComplexConjugate Real ArithmeticFunction.Moebius NumberTheorySymbols

namespace Ad3.S

def ee (x : ℂ) : ℂ := exp (2 * π * I * x)

def th (P : ℤ → ℂ) (ν : ℕ) (z : ℂ) : ℂ := ∑' n : ℤ, P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * z)

def GS (r : ℤ) (d : ℕ) : ℂ := ∑ x ∈ Finset.range d, ee (r * (x : ℂ) ^ 2 / d)

def KK (α β : ℂ) (y t : ℝ) : ℂ := ((y : ℂ) - I * t) ^ (-α) * ((y : ℂ) + I * t) ^ (-β)

def Phi (α β : ℂ) (ξ : ℝ) : ℂ := ∫ t : ℝ, KK α β 1 t * ee (-(ξ * t))

def al (k ν : ℕ) (s : ℂ) : ℂ := (s - k + ν + 1) / 2
def be (k ν : ℕ) (s : ℂ) : ℂ := (s + k - ν) / 2
def om (k ν : ℕ) (s : ℂ) : ℂ := (s + k + ν + 1) / 2

def NN (n : ℤ) (e : ℕ) : ℕ := ((Finset.range e).filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card

def RR (n : ℤ) (d : ℕ) : ℂ := ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d), GS r d * ee (-(n * r / d))

def Idx (L : ℕ) : Type := {p : ℕ × ℤ // 0 < p.1 ∧ IsCoprime ((L : ℤ) * p.2) (p.1 : ℤ)}

variable {M : ℕ}

def tm (c : DirichletCharacter ℂ M) (k ν : ℕ) (s : ℂ) (v : ℂ) (p : ℕ × ℤ) : ℂ :=
  c (p.1 : ZMod M) * (p.1 : ℂ) ^ (-(s + 1)) * GS p.2 p.1 * KK (al k ν s) (be k ν s) v.im (v.re - p.2 / p.1)

def Ep (c : DirichletCharacter ℂ M) (k ν : ℕ) (s : ℂ) (v : ℂ) : ℂ := ∑' p : Idx (4 * M ^ 2), tm c k ν s v p.1

def Dn (c : DirichletCharacter ℂ M) (n : ℤ) (s : ℂ) : ℂ := ∑' d : ℕ, c (d : ZMod M) * RR n d * (d : ℂ) ^ (-(s + 1))

def pref (L k ν : ℕ) (s : ℂ) (z : ℍ) : ℂ :=
  (z.im : ℂ) ^ om k ν s * (L : ℂ) ^ (-(s + 1 / 2)) / KK (al k ν s) (be k ν s) (-1 / (z : ℂ)).im (-1 / (z : ℂ)).re

def Ht (z : ℍ) : ℝ := (1 + ‖(z : ℂ)‖ ^ 2) / z.im

def strip : Set ℍ := {z | 0 ≤ z.re ∧ z.re < 1}

def FF (f : ℍ → ℂ) (ψ : DirichletCharacter ℂ M) (k ν : ℕ) (s : ℂ) (z : ℍ) : ℂ :=
  f z * conj (th (fun n => ψ⁻¹ (n : ZMod M)) ν z) * (z.im : ℂ) ^ om k ν s

def HP (a : ℝ) : Set ℂ := {s | a < s.re}

def T1 : Prop := ∀ (Q : ℤ → ℂ) (m ν : ℕ) (τ : ℂ), 0 < m → ν ≤ 1 → 0 < τ.im → (∀ x, Q (x + m) = Q x) →
  th Q ν τ = (-2 * I * τ) ^ (-(1 / 2 : ℂ)) * ((2 * τ * m) ^ ν)⁻¹ * (m : ℂ)⁻¹ *
    ∑' n : ℤ, (∑ x ∈ Finset.range m, Q x * ee (n * x / m)) * (n : ℂ) ^ ν * ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ)))

def T2 : Prop := ∀ (M d : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (a b c' n : ℤ), 0 < d →
  a * d - b * (4 * (M : ℤ) ^ 2 * c') = 1 →
  ∑ x ∈ Finset.range (M * d), ψ (x : ZMod M) * ee (b * (x : ℂ) ^ 2 / d) * ee (n * x / ((M * d : ℕ) : ℂ)) =
    ψ (d : ZMod M) * GS b d * ee (c' * (n : ℂ) ^ 2 / d) * ∑ x ∈ Finset.range M, ψ (x : ZMod M) * ee (n * x / M)

def T3 : Prop := ∀ (M d ν : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (c' : ℤ) (γ : SL(2, ℤ)) (z : ℍ), 0 < d → ν ≤ 1 →
  γ 1 0 = 4 * (M : ℤ) ^ 2 * c' → γ 1 1 = d →
  th (fun n => ψ (n : ZMod M)) ν (γ • z : ℍ) =
    ψ (d : ZMod M) * GS (γ 0 1) d * (d : ℂ) ^ (-(1 / 2 : ℂ)) * (-I * (d * (-1 / (z : ℂ)) - γ 1 0)) ^ (1 / 2 : ℂ) *
      (-I * (-1 / (z : ℂ))) ^ (-(1 / 2 : ℂ)) * ((d * (-1 / (z : ℂ)) - γ 1 0) / (-1 / (z : ℂ))) ^ ν *
      th (fun n => ψ (n : ZMod M)) ν z

def T4 : Prop := ∀ (M d : ℕ) (a b c' : ℤ), 0 < d → a * d - b * (4 * (M : ℤ) ^ 2 * c') = 1 → conj (GS b d) = GS c' d

def T5 : Prop := ∀ (k N M ν d : ℕ) [NeZero N] [NeZero M] (hM : N ∣ M) (χ : DirichletCharacter ℂ N) f a, IsForm k N χ f a →
  ∀ (c : DirichletCharacter ℂ M) (c' : ℤ) (γ : SL(2, ℤ)) (z : ℍ) (s : ℂ), 0 < d → ν ≤ 1 →
  γ 1 0 = 4 * (M : ℤ) ^ 2 * c' → γ 1 1 = d →
  FF f (c * DirichletCharacter.changeLevel hM χ⁻¹) k ν s (γ • z) =
    f z * conj (th (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (n : ZMod M)) ν z) * pref (4 * M ^ 2) k ν s z *
      tm c k ν s (-1 / (z : ℂ) / ((4 * M ^ 2 : ℕ) : ℂ)) (d, c')

def IsWt (L : ℕ) (β : ℍ → ℝ) : Prop := Measurable β ∧ (∀ z, 0 ≤ β z ∧ β z ≤ 1) ∧
  ∀ z, HasSum (fun γ : Gamma0 L => β ((γ : SL(2, ℤ)) • z)) 2

def U0 : Prop := ∀ L : ℕ, 0 < L → ∃ β, IsWt L β ∧ ∃ T : Finset SL(2, ℤ), ∀ z, β z ≠ 0 → ∃ σ ∈ T, σ⁻¹ • z ∈ 𝒟

def U1 : Prop := ∀ L : ℕ, 2 ≤ L → ∀ β, IsWt L β → ∀ γ : Idx L → SL(2, ℤ),
  (∀ p, γ p 1 0 = L * p.1.2 ∧ γ p 1 1 = p.1.1) → ∀ F : ℍ → ℂ, Measurable F → (∀ z, F ((1 : ℝ) +ᵥ z) = F z) →
  IntegrableOn F strip → ∫ z in strip, F z = ∫ z, (β z : ℂ) * ∑' p, F (γ p • z)

def B1 : Prop := ∀ (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) f a, IsForm k N χ f a → a 0 = 0 ∧ ∃ C : ℝ,
  (∀ z : ℍ, ‖f z‖ ≤ C * z.im ^ (-(k : ℝ) / 2)) ∧ (∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2)) ∧
    ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * Real.exp (-z.im)

def B2 : Prop := ∀ (P : ℤ → ℂ) (ν : ℕ), ν ≤ 1 → P 0 = 0 → (∀ n, ‖P n‖ ≤ 1) →
  (Continuous fun z : ℍ => th P ν z) ∧ (∀ z : ℍ, th P ν (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = th P ν z) ∧
  (∀ z : ℍ, Summable fun n : ℤ => ‖P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * z)‖) ∧
    ∃ C : ℝ, ∀ z : ℍ, ‖th P ν z‖ ≤ C * z.im ^ (-((ν : ℝ) + 1) / 2)

def HorizontalIntegralTwisted : Prop := ∀ (k N M ν : ℕ) [NeZero N] [NeZero M], 2 ≤ M → ∀ (χ : DirichletCharacter ℂ N) f a, IsForm k N χ f a →
  ∀ ψ : DirichletCharacter ℂ M, ν ≤ 1 → ψ (-1) = (-1) ^ ν → ∀ (y : ℝ) (hy : 0 < y),
  HasSum (fun n : ℕ => 2 * (ψ (n : ZMod M) * a (n ^ 2)) * (n : ℂ) ^ ν * (Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℂ))
    (∫ x in (0 : ℝ)..1, f ⟨x + y * I, by simpa using hy⟩ * conj (th (fun n => ψ⁻¹ (n : ZMod M)) ν (x + y * I)))

def U2 : Prop := ∀ (k N M ν : ℕ) [NeZero N] [NeZero M], 2 ≤ M → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) f a,
  IsForm k N χ f a → ∀ ψ : DirichletCharacter ℂ M, ν ≤ 1 → ψ (-1) = (-1) ^ ν → ∀ s : ℂ, 2 < s.re →
  IntegrableOn (FF f ψ k ν s) strip ∧ ∫ z in strip, FF f ψ k ν s z =
    2 * Gamma (om k ν s - 1) * (4 * π : ℂ) ^ (1 - om k ν s) * LSeries (fun n => ψ n * a (n ^ 2)) (s + k - 1)

def D1 : Prop := ∀ (k N : ℕ) [NeZero N] (f : CuspForm (Gamma1 N) (k : ℤ)) (σ : SL(2, ℤ)) (A : ℕ),
  IntegrableOn (fun z : ℍ => ‖f z‖ * Ht z ^ A) {z | σ⁻¹ • z ∈ 𝒟}

def LB : Prop := ∃ C : ℝ, ∀ (q : ℕ) (Φ : ℕ → ℂ), 0 < q → (∀ n, Φ (n + q) = Φ n) → (∀ n, ‖Φ n‖ ≤ 1) →
  ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (HP (-1)) ∧ (∀ s : ℂ, 1 < s.re → G s = (s - 1) * LSeries Φ s) ∧
    ∀ s : ℂ, -1 / 2 ≤ s.re → ‖G s‖ ≤ C * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4

def N1 : Prop := ∀ (n : ℤ) (d : ℕ), 0 < d → RR n d = d * ∑ e ∈ d.divisors, ((μ (d / e) : ℤ) : ℂ) * (NN n e : ℂ)

def N2 : Prop := ∀ n : ℤ, NN n 1 = 1 ∧ (∀ e, NN n e ≤ e) ∧ (∀ e e', Nat.Coprime e e' → NN n (e * e') = NN n e * NN n e') ∧
  ∀ p j : ℕ, p.Prime → p ≠ 2 → ((¬ (p : ℤ) ∣ n → (NN n (p ^ (j + 1)) : ℤ) = 1 + J(n | p)) ∧
    (n ≠ 0 → NN n (p ^ j) ≤ 2 * p ^ n.natAbs.factorization p) ∧ (n = 0 → NN n (p ^ j) = p ^ (j / 2)))

def A2 : Prop := ∀ (M : ℕ) [NeZero M] (c : DirichletCharacter ℂ M) (n : ℤ) (s : ℂ), 2 < s.re →
  (Summable fun d : ℕ => ‖c (d : ZMod M) * RR n d * (d : ℂ) ^ (-(s + 1))‖) ∧
  HasProd (fun p : Nat.Primes => (∑' j : ℕ, (NN n ((p : ℕ) ^ j) : ℂ) * (c ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-s)) ^ j) /
      (1 + c ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-s)))
    (DirichletCharacter.LFunction (c ^ 2) (2 * s) * Dn c n s)

def A1 : Prop := ∀ (M : ℕ) [NeZero M], 2 ∣ M → ∀ c : DirichletCharacter ℂ M, ∃ (C : ℝ) (B : ℕ), ∀ n : ℤ, n ≠ 0 →
  ∃ A : ℂ → ℂ, DifferentiableOn ℂ A (HP (1 / 4)) ∧
    (∀ s : ℂ, 2 < s.re → A s = (s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s) * Dn c n s) ∧
    ∀ s : ℂ, 1 / 4 < s.re → ‖A s‖ ≤ C * |(n : ℝ)| ^ B * (1 + ‖s‖) ^ 4

def A0 : Prop := ∀ (M : ℕ) [NeZero M], 2 ∣ M → ∀ c : DirichletCharacter ℂ M, ∃ (C : ℝ) (A : ℂ → ℂ),
  DifferentiableOn ℂ A (HP (1 / 4)) ∧
    (∀ s : ℂ, 2 < s.re → (s - 1 / 2) * A s = (s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s) * Dn c 0 s) ∧
    ∀ s : ℂ, 1 / 4 < s.re → ‖A s‖ ≤ C * (1 + ‖s‖) ^ 4

def W0 : Prop := ∀ a b : ℝ,
  (∀ ξ : ℝ, DifferentiableOn ℂ (fun s : ℂ => Phi (s / 2 + a) (s / 2 + b) ξ) (HP (1 - a - b))) ∧
  (∀ s ∈ HP (1 - a - b), (Integrable fun t => KK (s / 2 + a) (s / 2 + b) 1 t) ∧
    Continuous fun ξ => Phi (s / 2 + a) (s / 2 + b) ξ) ∧
  ∀ δ B : ℝ, 0 < δ → ∃ C : ℝ, ∀ (s : ℂ) (ξ : ℝ), 1 - a - b + δ ≤ s.re → s.re ≤ B →
    ‖Phi (s / 2 + a) (s / 2 + b) ξ‖ ≤ C * Real.exp (C * s.im ^ 2)

def W1 : Prop := ∀ α β : ℂ, 1 < (α + β).re →
  (∀ ξ : ℝ, 2 * π * ξ * Phi α β ξ = α * Phi (α + 1) β ξ - β * Phi α (β + 1) ξ) ∧
    (α + β - 1) * Phi α β 0 = 2 * α * Phi (α + 1) β 0

def W2 : Prop := ∀ (m : ℕ) (a b : ℝ), ∃ Ψ : ℂ → ℝ → ℂ,
  (∀ ξ, DifferentiableOn ℂ (fun s => Ψ s ξ) (HP (1 - a - b - m))) ∧ (∀ s ∈ HP (1 - a - b - m), Measurable (Ψ s)) ∧
  (∀ s ∈ HP (1 - a - b), ∀ ξ, ξ ≠ 0 → Ψ s ξ = Phi (s / 2 + a) (s / 2 + b) ξ) ∧
  ∀ δ B : ℝ, 0 < δ → ∃ C : ℝ, ∀ (s : ℂ) (ξ : ℝ), ξ ≠ 0 → 1 - a - b - m + δ ≤ s.re → s.re ≤ B →
    ‖Ψ s ξ‖ ≤ C * Real.exp (C * s.im ^ 2) / |ξ| ^ m

def P1 : Prop := ∀ (s α β : ℂ) (a b y : ℝ), α = s / 2 + a → β = s / 2 + b → 1 < (α + β).re → 0 < y →
  (∃ C : ℝ, ∀ t : ℝ, (Summable fun j : ℤ => ‖KK α β y (t - j)‖) ∧ ∑' j : ℤ, ‖KK α β y (t - j)‖ ≤ C) ∧
  (Summable fun n : ℤ => ‖Phi α β (n * y)‖) ∧
  ∀ t : ℝ, ∑' j : ℤ, KK α β y (t - j) = ∑' n : ℤ, (y : ℂ) ^ (1 - α - β) * Phi α β (n * y) * ee (n * t)

def P2 : Prop := ∀ (M k ν : ℕ) [NeZero M], 2 ∣ M → ∀ (c : DirichletCharacter ℂ M) (s v : ℂ), 2 < s.re → 0 < v.im →
  Ep c k ν s v = ∑' n : ℤ, Dn c n s * (v.im : ℂ) ^ (1 / 2 - s) * Phi (al k ν s) (be k ν s) (n * v.im) * ee (n * v.re)

def E0 : Prop := ∀ (M k ν : ℕ) [NeZero M], 2 ∣ M → ∀ c : DirichletCharacter ℂ M, ∃ Es : ℂ → ℂ → ℂ,
  (∀ v : ℂ, 0 < v.im → DifferentiableOn ℂ (fun s => Es s v) (HP (1 / 4))) ∧ (∀ s ∈ HP (1 / 4), Measurable (Es s)) ∧
  (∀ s v : ℂ, 2 < s.re → 0 < v.im → Es s v = (s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s) * Ep c k ν s v) ∧
  ∀ b : ℝ, ∃ (C : ℝ) (A : ℕ), ∀ s v : ℂ, 1 / 4 < s.re → s.re ≤ b → 0 < v.im →
    ‖Es s v‖ ≤ C * Real.exp (C * s.im ^ 2) * (v.im ^ A + v.im⁻¹ ^ A)

def PR : Prop := ∀ L k ν : ℕ, 0 < L → (∀ z, Differentiable ℂ fun s => pref L k ν s z) ∧ (∀ s, Measurable (pref L k ν s)) ∧
  (∀ b : ℝ, ∃ (C : ℝ) (A : ℕ), ∀ (s : ℂ) (z : ℍ), 0 ≤ s.re → s.re ≤ b → ‖pref L k ν s z‖ ≤ C * Real.exp (C * s.im ^ 2) * Ht z ^ A) ∧
  ∀ z : ℍ, 1 ≤ Ht z ∧ z.im⁻¹ ≤ Ht z ∧ 0 < (-1 / (z : ℂ) / (L : ℂ)).im ∧ (-1 / (z : ℂ) / (L : ℂ)).im ≤ Ht z ∧
    (-1 / (z : ℂ) / (L : ℂ)).im⁻¹ ≤ L * Ht z

def G0 : Prop := ∀ a b : ℝ, ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖(Gamma z)⁻¹‖ ≤ C * Real.exp (C * z.im ^ 2)

def HI : Prop := ∀ (X : Type) [MeasurableSpace X] (m : Measure X) (U : Set ℂ) (F : ℂ → X → ℂ), IsOpen U →
  (∀ s ∈ U, AEStronglyMeasurable (F s) m) → (∀ x, DifferentiableOn ℂ (fun s => F s x) U) →
  (∀ s₀ ∈ U, ∃ g : X → ℝ, Integrable g m ∧ ∀ᶠ s in 𝓝 s₀, ∀ x, ‖F s x‖ ≤ g x) →
  DifferentiableOn ℂ (fun s => ∫ x, F s x ∂m) U

def S1 : Prop := ∀ (k N M ν : ℕ) [NeZero N] [NeZero M] (hM : N ∣ M), 4 ∣ M → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) f a,
  IsForm k N χ f a → ∀ c : DirichletCharacter ℂ M, ν ≤ 1 → (c * DirichletCharacter.changeLevel hM χ⁻¹) (-1) = (-1) ^ ν →
  ∀ β, IsWt (4 * M ^ 2) β → ∀ s : ℂ, 2 < s.re →
    ∫ z : ℍ, (β z : ℂ) * (f z * conj (th (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (n : ZMod M)) ν z) *
        pref (4 * M ^ 2) k ν s z * Ep c k ν s (-1 / (z : ℂ) / ((4 * M ^ 2 : ℕ) : ℂ))) =
      2 * Gamma (om k ν s - 1) * (4 * π : ℂ) ^ (1 - om k ν s) *
        LSeries (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹) n * a (n ^ 2)) (s + k - 1)

def E1 : Prop := ∀ c : HeckeCharacter ℚ, IsOfFinOrder c → ∀ M₀ : ℕ, 0 < M₀ → ∃ (M : ℕ) (_ : NeZero M) (c' : DirichletCharacter ℂ M),
  M₀ ∣ M ∧ ∀ v : Pl, ¬ pOf v ∣ M → c' (pOf v : ZMod M) = (localChar c v (unifUnit (Qv v)) : ℂ)

def faceMap_comp_succAbove_castSucc : Prop := (∃ e : Pl ≃ Nat.Primes, ∀ v, (e v : ℕ) = pOf v) ∧
  ∀ (v : Pl) (μ' : (Qv v)ˣ →* ℂˣ), IsUnramifiedChar μ' → ∀ s : ℂ,
    localLFactor μ' s = (1 - (μ' (unifUnit (Qv v)) : ℂ) * (pOf v : ℂ) ^ (-s))⁻¹

def E2a : Prop := ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a →
  (∀ m n, Nat.Coprime m n → a (m * n) = a m * a n) ∧ ∀ p : ℕ, p.Prime → ∀ α β : ℂ, α + β = a p →
    α * β = χ p * (p : ℂ) ^ (k - 1) → ∀ j, a (p ^ j) = ∑ i ∈ Finset.range (j + 1), α ^ i * β ^ (j - i)

def E2b : Prop := ∀ r X : ℂ, ‖r‖ = 1 → ‖X‖ < 1 →
  HasSum (fun j : ℕ => (∑ i ∈ Finset.range (2 * j + 1), r ^ i) * (r⁻¹ * X) ^ j)
    ((1 - X ^ 2) * ((1 - r * X)⁻¹ * (1 - X)⁻¹ * (1 - r⁻¹ * X)⁻¹))

def E2 : Prop := ∀ (N M : ℕ) [NeZero N] [NeZero M] (hM : N ∣ M) (χ : DirichletCharacter ℂ N) (D : Dat) (a : ℕ → ℂ),
  IsEig D.k N χ a → SatOf N χ a D → ∀ c δ T, admitted D c δ T → (∀ v, v ∈ T ↔ pOf v ∣ M) → ∀ c' : DirichletCharacter ℂ M,
  (∀ v : Pl, ¬ pOf v ∣ M → c' (pOf v : ZMod M) = (localChar c v (unifUnit (Qv v)) : ℂ)) → ∀ s : ℂ, 2 < s.re →
    eul D c T s = DirichletCharacter.LFunction (c' ^ 2) (2 * s) *
      LSeries (fun n => (c' * DirichletCharacter.changeLevel hM χ⁻¹) n * a (n ^ 2)) (s + D.k - 1)

open Classical in

def E3 : Prop := ∀ D c δ S, admitted D c δ S → DifferentiableOn ℂ (eul D c S) (HP 1) ∧
  (∀ T : Finset Pl, S ⊆ T → ∀ s : ℂ, 1 < s.re →
    eul D c S s = (∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s) * eul D c T s) ∧
  ∀ v ∉ S, DifferentiableOn ℂ (lf3 (D.ν v) (localChar c v)) (HP 0) ∧
    ∃ C : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → ‖lf3 (D.ν v) (localChar c v) s‖ ≤ C

end Ad3.S

end
