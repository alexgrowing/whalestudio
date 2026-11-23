import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Lat {n : ℕ} (A : AddSubgroup (Fin n → k)) : Prop :=
  IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k))

def perp (ψ : AddChar k Circle) {n : ℕ} (A : AddSubgroup (Fin n → k)) : AddSubgroup (Fin n → k) where
  carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
  add_mem' := by
    intro x y hx hy a ha
    rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  zero_mem' := by
    intro a _
    simp
  neg_mem' := by
    intro x hx a ha
    rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one]

theorem mem_perp (ψ : AddChar k Circle) {n : ℕ} (A : AddSubgroup (Fin n → k)) (ξ : Fin n → k) :
    ξ ∈ perp ψ A ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1 := Iff.rfl

def gmap {n : ℕ} (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) : AddSubgroup (Fin n → k) :=
  A.map (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def AD (ψ : AddChar k Circle) {n : ℕ} (col : (Fin n → k) → V →ₗ[ℂ] V) (ξ : Fin n → k) (A : AddSubgroup (Fin n → k))
    (v : V) (p : AddSubgroup (Fin n → k) × Finset (Fin n → k)) : Prop :=
  p.1 ≤ A ∧ IsOpen (p.1 : Set (Fin n → k)) ∧ (∀ a ∈ p.1, col a v = v) ∧ (∀ a ∈ p.1, ψ (ξ ⬝ᵥ a) = 1) ∧
    (∀ t ∈ p.2, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ p.2 ∧ a - t ∈ p.1

open Classical in

def av (ψ : AddChar k Circle) {n : ℕ} (col : (Fin n → k) → V →ₗ[ℂ] V) (ξ : Fin n → k) (A : AddSubgroup (Fin n → k))
    (v : V) : V :=
  if hd : ∃ p, AD ψ col ξ A v p then
    ((hd.choose.2.card : ℂ)⁻¹) • ∑ t ∈ hd.choose.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v
  else 0

def Psd (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ ∀ v, 0 ≤ (B v v).re

structure Setup {m : ℕ} (col : (Fin (m + 1) → k) → V →ₗ[ℂ] V) (gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)) : Prop where
  col_zero : ∀ v, col 0 v = v
  col_add : ∀ x y v, col (x + y) v = col x (col y v)
  conj : ∀ g x v, gl g (col x v) = col ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) (gl g v)
  smooth_col : ∀ v, IsOpen {x | col x v = v}
  smooth_gl : ∀ v, IsOpen {g : GL (Fin (m + 1)) k | gl g v = v}

def xz (m : ℕ) : Fin (m + 1) → k := Pi.single (Fin.last m) 1

def IsD (ψ : AddChar k Circle) {m : ℕ} (col : (Fin (m + 1) → k) → V →ₗ[ℂ] V) (A₀ : AddSubgroup (Fin (m + 1) → k))
    (B B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ v w, ∃ A₁, Lat A₁ ∧ A₀ ≤ A₁ ∧ ∀ A, Lat A → A₁ ≤ A →
    B' v w = ((A₀.relIndex A : ℕ) : ℂ) * B (av ψ col (xz m) A v) w

def IsA {m : ℕ} (col : (Fin (m + 1) → k) → V →ₗ[ℂ] V) (B B₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ v w, Filter.Tendsto (fun A : {A : AddSubgroup (Fin (m + 1) → k) // Lat A} =>
      B (av (1 : AddChar k Circle) col 0 A.1 v) w) Filter.atTop (nhds (B₀ v w))

def AbsLift : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (col : (Fin (m + 1) → k) → V →ₗ[ℂ] V) (gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)), Setup col gl →
    ∀ (s : ℝ) (B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (A₀ : AddSubgroup (Fin (m + 1) → k)), Lat A₀ →
    Psd B → (∀ x v w, B (col x v) (col x w) = B v w) →
    (∀ g v w, B (gl g v) (gl g w) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * B v w) →
    IsD ψ col A₀ B B' → Psd C → (∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w) →
    (∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((nabs k (Matrix.GeneralLinearGroup.det p) ^ (s + 1) : ℝ) : ℂ) * C v w) →
    (∀ v, (C v v).re ≤ (B' v v).re) →
    ∃ I : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, Psd I ∧ (∀ x v w, I (col x v) (col x w) = I v w) ∧
      (∀ g v w, I (gl g v) (gl g w) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * I v w) ∧
      (∀ v, (I v v).re ≤ (B v v).re) ∧ IsD ψ col A₀ I C ∧ IsA col I 0 ∧
      ∀ Y : Submodule ℂ V, (∀ g, ∀ y ∈ Y, gl g y ∈ Y) → (∀ y ∈ Y, ∀ w, C y w = 0) → ∀ y ∈ Y, ∀ w, I y w = 0

end PositivityTheory.RgUd.Form.U.Lift2
