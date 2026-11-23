import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import GroundTheory.AutomorphicForms.MeasuresModulus

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace CompanionTheory.JacquetShalikaLocal

variable {F : Type} [Field F] {n : ℕ}

def cM (n k : ℕ) (x : Fin (k + 1) → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if h : (j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1 then x ⟨i, h.2⟩ else 0

theorem cM_mul (k : ℕ) (x y : Fin (k + 1) → F) : cM n k x * cM n k y = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [cM, Matrix.of_apply]
  by_cases h : (l : ℕ) = k + 1
  · rw [dif_neg (c := (j : ℕ) = k + 1 ∧ (l : ℕ) < k + 1) (fun h' => by omega), mul_zero]
  · rw [dif_neg (c := (l : ℕ) = k + 1 ∧ (i : ℕ) < k + 1) (fun h' => h h'.1), zero_mul]

def col (n k : ℕ) (x : Fin (k + 1) → F) : GL (Fin n) F where
  val := 1 + cM n k x
  inv := 1 - cM n k x
  val_inv := by rw [mul_sub, mul_one, add_mul, one_mul, cM_mul, add_zero, add_sub_cancel_right]
  inv_val := by rw [sub_mul, one_mul, mul_add, mul_one, cM_mul, add_zero, add_sub_cancel_right]

def inP (m : ℕ) (g : GL (Fin n) F) : Prop :=
  (∀ i j : Fin n, m ≤ (i : ℕ) → g i j = (1 : Matrix (Fin n) (Fin n) F) i j) ∧
    ∀ i j : Fin n, m < (j : ℕ) → g i j = (1 : Matrix (Fin n) (Fin n) F) i j

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def inU (m : ℕ) (g : GL (Fin n) F) : Prop :=
  g ∈ unipotent F n ∧ ∀ i j : Fin n, (j : ℕ) ≤ m → g i j = (1 : Matrix (Fin n) (Fin n) F) i j

def Div {ι : Type} (c : ℕ) (A : Matrix ι ι F) : Prop := ∀ i j, ∃ y ∈ 𝒪[F], A i j = (uniformizer F : F) ^ c * y

variable (F) in

def lat (m M : ℕ) : Set (Fin m → F) := {x | ∀ i, (uniformizer F : F) ^ M * x i ∈ 𝒪[F]}

def PsiOK (ψ : AddChar F ℂ) : Prop :=
  (∀ x ∈ 𝒪[F], ψ x = 1) ∧ (∃ x : F, (uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ x ≠ 1) ∧ ∀ x, ‖ψ x‖ = 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def Smooth (ρ : Representation ℂ (GL (Fin n) F) V) : Prop :=
  ∀ u, ∃ c : ℕ, ∀ g : GL (Fin n) F, Div (c + 1) ((g : Matrix (Fin n) (Fin n) F) - 1) → ρ g u = u

def Whit (ρ : Representation ℂ (GL (Fin n) F) V) (ψ : AddChar F ℂ) (l : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ g ∈ unipotent F n, ∀ u, l (ρ g u) = Whittaker.psiN ψ g * l u

def Unit' (ρ : Representation ℂ (GL (Fin n) F) V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop :=
  (∀ u u', starRingEnd ℂ (B u u') = B u' u) ∧ (∀ u, u ≠ 0 → 0 < (B u u).re) ∧ ∀ g u u', B (ρ g u) (ρ g u') = B u u'

def Heig (ρ : Representation ℂ (GL (Fin n) F) V) (v : V) (z : Fin n → ℂˣ) : Prop :=
  (∀ g ∈ integralGL F n, ρ g v = v) ∧ ∀ r ≤ n,
    ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n, (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v =
      (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r)) • v

structure Inv (ρ : Representation ℂ (GL (Fin n) F) V) (ψ : AddChar F ℂ) (l : V →ₗ[ℂ] ℂ) (m : ℕ)
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  herm : ∀ u u', starRingEnd ℂ (B u u') = B u' u
  psd : ∀ u, 0 ≤ (B u u).re
  null : ∀ u, B u u = 0 → l u = 0
  quasi : ∀ g, inP m g → ∀ u u', B (ρ g u) (ρ g u') =
    (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - m) * B u u'
  equi : ∀ g, inU m g → ∀ u u', B u' (ρ g u) = Whittaker.psiN ψ g * B u' u

variable [MeasurableSpace F]

def Char (μ : Measure F) (ρ : Representation ℂ (GL (Fin n) F) V) (ψ : AddChar F ℂ) (k : ℕ)
    (B B' : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop :=
  ∀ u u', ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → B' u' u =
    ∫ x in lat F (k + 1) M, ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u) ∂(Measure.pi fun _ => μ)

end CompanionTheory.JacquetShalikaLocal

end
