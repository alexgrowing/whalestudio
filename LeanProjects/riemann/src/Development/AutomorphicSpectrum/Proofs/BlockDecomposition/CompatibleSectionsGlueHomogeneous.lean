import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveCharts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Saturation

noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.SerreVan

variable {B : Type} [CommRing B] {M : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem comp_mul {a : MvPolynomial (Fin M) B} {e : ℕ} (ha : a.IsHomogeneous e) (d : ℕ)
    (f : MvPolynomial (Fin M) B) :
    homogeneousComponent (e + d) (a * f) = a * homogeneousComponent d f := by
  have h := DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin M) B)
    (i := e) (j := d) (a := a) (b := f) ha
  rw [← decomposition.decompose'_apply, ← decomposition.decompose'_apply]
  exact h

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem comp_zero_X_mul (i : Fin M) (f : MvPolynomial (Fin M) B) :
    homogeneousComponent 0 (X i * f) = 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem_of_not_le (homogeneousSubmodule (Fin M) B)
    (i := 1) (n := 0) (a := X i) (b := f) (isHomogeneous_X B i) (by norm_num)
  rw [← decomposition.decompose'_apply]
  exact h

noncomputable def sat {R : Type} [CommRing R] (Q : Ideal R) (x : R) : Ideal R :=
  _root_.UpperTheory.Reformulated.B.IdealSaturationByElement.sat Q x

def V0 (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ f ∈ P, f.IsHomogeneous n → (∀ i ∈ W, ∃ m : ℕ, X i ^ m * f ∈ Q) → f ∈ Q

def V1 (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin M → MvPolynomial (Fin M) B),
    (∀ i ∈ W, f i ∈ P ∧ (f i).IsHomogeneous (n + k)) →
    (∀ i ∈ W, ∀ j ∈ W, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ Q) →
    ∃ g ∈ P, g.IsHomogeneous n ∧ ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ Q

section Extension

variable {W : Finset (Fin M)} {P P' Q : Ideal (MvPolynomial (Fin M) B)} {n₀ : ℕ}

end Extension

section Steps

variable {W : Finset (Fin M)} {P P' Q : Ideal (MvPolynomial (Fin M) B)} {n₀ : ℕ}

end Steps

section Base

variable {P Q : Ideal (MvPolynomial (Fin M) B)}

end Base

section Main

variable {P Q : Ideal (MvPolynomial (Fin M) B)}

theorem charts [IsNoetherianRing B] (W : Finset (Fin M)) :
    ∀ P Q : Ideal (MvPolynomial (Fin M) B), HomogIdeal P → HomogIdeal Q → Q ≤ P →
      (∀ j, j ∉ W → ∃ k : ℕ, ∀ f ∈ P, X j ^ k * f ∈ Q) →
      ∃ n₀, V0 W P Q n₀ ∧ V1 W P Q n₀ :=
  _root_.UpperTheory.Reformulated.B.ProjectiveCharts.charts W

theorem serre_vanishing : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (N : ℕ)
    (P : Ideal (MvPolynomial (Fin (N + 1)) B)), HomogIdeal P →
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin (N + 1) → MvPolynomial (Fin (N + 1)) B),
      (∀ i, (f i).IsHomogeneous (n + k)) →
      (∀ i j, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ P) →
      ∃ g : MvPolynomial (Fin (N + 1)) B, g.IsHomogeneous n ∧
        ∀ i, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ P := by
  intro B _ _ N P hP
  obtain ⟨n₀, -, h⟩ := charts (B := B) (M := N + 1) Finset.univ ⊤ P (fun _ _ _ => trivial) hP
    le_top (fun j hj => absurd (Finset.mem_univ j) hj)
  refine ⟨n₀, fun n hn k f hf hc => ?_⟩
  obtain ⟨g, -, hgh, hg⟩ := h n hn k f (fun i _ => ⟨trivial, hf i⟩)
    (fun i _ j _ => hc i j)
  exact ⟨g, hgh, fun i => hg i (Finset.mem_univ i)⟩

end Main

end GlobalTheory.CompanionTheory.GE.SerreVan
