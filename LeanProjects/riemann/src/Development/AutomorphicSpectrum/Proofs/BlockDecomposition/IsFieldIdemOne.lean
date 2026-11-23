import Mathlib

open MeasureTheory Topology Filter
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

variable {A : Type} [CommRing A]

structure IsFieldIdem (f : A) : Prop where
  idem : f * f = f
  ne : f ≠ 0
  inv : ∀ x, f * x ≠ 0 → ∃ y, f * x * y = f

structure IsFieldDec {ι : Type} [Fintype ι] (e : A) (f : ι → A) : Prop where
  field : ∀ i, IsFieldIdem (f i)
  orth : ∀ i j, i ≠ j → f i * f j = 0
  sum : ∑ i, f i = e

def NonDiscreteAt [TopologicalSpace A] (f : A) : Prop := ∀ V ∈ 𝓝 (0 : A), ∃ x ∈ V, x ≠ 0 ∧ f * x = x

def IsHaarMod [TopologicalSpace A] [MeasurableSpace A] (md : Aˣ →* ℝ≥0) : Prop :=
  ∀ h : Measure A, h.IsAddHaarMeasure → ∀ u : Aˣ, h.map (fun x => (u : A) * x) = ((md u : ℝ≥0∞))⁻¹ • h

abbrev Fx (A : Type) (m n : ℕ) : Type := Matrix (Fin m) (Fin n) A

variable {a r t : ℕ}

def yc (P : Fx A a r → Fx A r a) (z : Fx A a r × Fx A a t) : Fx A r t := P z.1 * z.2

def vc (P : Fx A a r → Fx A r a) (z : Fx A a r × Fx A a t) : Fx A a t := z.2 - z.1 * yc P z

def admitted (e : A) (P : Fx A a r → Fx A r a) : Set (Fx A a r × Fx A a t) :=
  {z | e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ P z.1 * z.1 = e • (1 : Fx A r r)}

def Piece (e f : A) (P : Fx A a r → Fx A r a) (i : Fin t) (C : Set A) : Set (Fx A a r × Fx A a t) :=
  {z | z ∈ admitted e P ∧ (∀ p q, z.1 p q ∈ C) ∧ (∀ l k, f * yc P z l k ∈ C ∧ (1 - f) * yc P z l k ∈ C) ∧
    (∀ p k, k ≠ i → vc P z p k ∈ C) ∧ (∀ p, (1 - f) * vc P z p i ∈ C) ∧
    ∃ c : Fin t → A, c i = 0 ∧ (∀ k, f * c k = c k ∧ c k ∈ C) ∧ ∀ p, f * vc P z p i = ∑ k, c k * vc P z p k}

def gU (i : Fin t) (c₀ : Fin t → A) : Fx A t t := 1 + Matrix.of fun k j => if j = i then c₀ k else 0

def gD (i : Fin t) (u : A) : Fx A t t := Matrix.diagonal (Function.update 1 i u)

def yU (i : Fin t) (y₀ : Fin r → A) : Fx A r t := Matrix.of fun l j => if j = i then y₀ l else 0

end GlobalTheory.CompanionTheory.NullFr
