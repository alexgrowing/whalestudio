import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec

noncomputable section

open MeasureTheory Matrix Set
open scoped NNReal

namespace PositivityTheory.Rg.Sw

variable {m n : ℕ}

def GR (n : ℕ) : Subgroup (GL (Fin n ⊕ Fin n) ℂ) where
  carrier := {g | InG g.1}
  one_mem' := by simp [InG]
  mul_mem' := by
    intro a b ha hb
    simp only [InG, Set.mem_ofPred_eq, Units.val_mul, Matrix.conjTranspose_mul] at *
    calc b.1ᴴ * a.1ᴴ * JJ n * (a.1 * b.1) = b.1ᴴ * (a.1ᴴ * JJ n * a.1) * b.1 := by simp only [Matrix.mul_assoc]
      _ = JJ n := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [InG, Set.mem_ofPred_eq] at *
    have h1 : a.1 * (a⁻¹).1 = 1 := by simp
    calc (a⁻¹).1ᴴ * JJ n * (a⁻¹).1 = (a⁻¹).1ᴴ * (a.1ᴴ * JJ n * a.1) * (a⁻¹).1 := by rw [ha]
      _ = (a.1 * (a⁻¹).1)ᴴ * JJ n * (a.1 * (a⁻¹).1) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [h1]; simp

def mR (g : GR n) : M2 n := g.1.1

def cnt (ε : Fin m → Bool) (b : Bool) : ℕ := (Finset.univ.filter fun a => ε a = b).card

def F0 (p q : ℕ) (e : ℤ) (g : GR n) : ℂ := (mR g).det ^ e * f0 p q (mR g)

def hLoc (g : GR n) : ℝ := (‖(u1 (mR g)).det‖ ^ 2)⁻¹

def dil (c : ℝ) (X : Fin n → ℝ) : PX m n →ₗ[ℂ] PX m n :=
  ∑ j, (X j : ℂ) • ((m : ℂ) • LinearMap.id + ∑ a : Fin m,
    (LinearMap.mulLeft ℂ (MvPolynomial.X (a, j, false)) ∘ₗ (MvPolynomial.pderiv (a, j, false)).toLinearMap +
      LinearMap.mulLeft ℂ (MvPolynomial.X (a, j, true)) ∘ₗ (MvPolynomial.pderiv (a, j, true)).toLinearMap -
      (2 * c : ℂ) • LinearMap.mulLeft ℂ (MvPolynomial.X (a, j, false) * MvPolynomial.X (a, j, true))))

def IsDil (X : Fin n → ℝ) (t : ℝ) (a : GR n) : Prop :=
  mR a = fromBlocks (diagonal fun j => (Real.exp (t * X j) : ℂ)) 0 0 (diagonal fun j => (Real.exp (-(t * X j)) : ℂ))

structure LocData (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n) : Prop where
  cpos : 0 < c
  sign : (t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true)
  cont : ∀ P, Continuous (sL P)
  vac : ∀ g, sL 1 g = F0 p q e g
  law : ∀ P (y g : GR n), (mR y).toBlocks₂₁ = 0 → sL P (y * g) = F0 p q e y * sL P g
  cell : ∃ C : ℂ, C ≠ 0 ∧ ∀ P (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
    sL P g = C * secN ε c t P b
  kact : ∀ P (g k : GR n), InK (mR k) → sL P (g * k) = sL (ρ k P) g
  kvac : ∀ k : GR n, InK (mR k) → ρ k 1 = F0 p q e k • 1
  kfin : ∀ P, ∃ W : Submodule ℂ (PX m n), FiniteDimensional ℂ W ∧ P ∈ W ∧ (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) ∧
    ∀ Q ∈ W, ∀ l : PX m n →ₗ[ℂ] ℂ, ContinuousOn (fun k : GR n => l (ρ k Q)) {k | InK (mR k)}

structure GlobData (ε : Fin m → Bool) (c : ℝ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (ρ : GR n → PX m n →ₗ[ℂ] PX m n)
    (G : Type) [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
    (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)) : Prop where
  ιcont : Continuous ι
  split : ∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
    ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ ∀ P, sec P (x * ι y') = S * sL P y'
  Icont : Continuous (I 1)
  Ileft : ∀ γ ∈ Γ, ∀ g, I 1 (γ * g) = I 1 g
  Ik : ∀ P g (k : GR n), InK (mR k) → I P (g * ι k) = I (ρ k P) g
  Iinv : ∀ g a b P, I (hOp ε c a b P) g = 0
  Idil : ∀ (g : G) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (F : GR n → ℂ → ℂ), IsOpen U ∧
    (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (univ ×ˢ U) ∧ ∀ y, DifferentiableOn ℂ (F y) U ∧
      (∀ t : ℝ, F y t = I 1 (g * ι (y * a t))) ∧ ∀ r : ℕ, iteratedDeriv r (F y) 0 = I ((dil c X ^ r) 1) (g * ι y)
  eis : ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G → ℂ) (σ : ℝ), IsOpen U ∧ GlobalTheory.Cont.IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (E · g) U) ∧ ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ) ∧
    (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) ∧
    ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g q‖ ≤ u q) ∧
      ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g
  Λadd : ∀ l ∈ Λ, ∀ (a : ℂ) (F F' : G → ℂ), Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
    (∀ γ ∈ Γ, ∀ g, F' (γ * g) = F' g) → l (a • F + F') = a * l F + l F'
  Λbd : ∀ l ∈ Λ, ∃ C : Set G, IsCompact C ∧ ∀ (F : G → ℂ) (M : ℝ), Continuous F → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
    (∀ x ∈ C, ‖F x‖ ≤ M) → ‖l F‖ ≤ M
  Λsing : ∀ F : G → ℂ, Continuous F → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) → (∀ l ∈ Λ, l F = 0) →
    ∀ ψ, IsSingTest ψ → ∀ (nb : (Fin n → Fin n → ℝ) → GR n), (∀ x, mR (nb x) = nU (herm x)) →
      ∀ (g : G) (a b : GR n), ∫ x, F (g * ι (a * nb x * b)) * ψ x = 0
  Λval : ∀ l ∈ Λ, GlobalTheory.Cont.HolValueAt
    (fun z => l (GlobalTheory.Eis.cosetSum Pp Γ fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x)) s₀ (l (I 1))

def AbsThm : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → GoodSig n p q →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)), GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ →
      ∀ P g, GlobalTheory.Cont.HolValueAt
        (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec P x) g) s₀ (I P g)

end PositivityTheory.Rg.Sw
