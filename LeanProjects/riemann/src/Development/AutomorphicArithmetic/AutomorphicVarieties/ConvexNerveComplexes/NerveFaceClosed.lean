import Mathlib

open Set

namespace UpperTheory.V.ConeExtensionAcyclic

abbrev Ch (I : Type*) (n : ℕ) := (Fin n → I) →₀ ℤ

noncomputable def bd (I : Type*) (n : ℕ) : Ch I (n + 1) →ₗ[ℤ] Ch I n :=
  Finsupp.linearCombination ℤ fun t : Fin (n + 1) → I =>
    ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (t ∘ j.succAbove) (1 : ℤ)

def FaceClosed {I : Type*} (S : ∀ n, Set (Fin n → I)) : Prop :=
  ∀ n (t : Fin (n + 1) → I), t ∈ S (n + 1) → ∀ j : Fin (n + 1), t ∘ j.succAbove ∈ S n

def Acyc {I : Type*} (S : ∀ n, Set (Fin n → I)) : Prop :=
  (∀ c ∈ Finsupp.supported ℤ ℤ (S 0), ∃ b ∈ Finsupp.supported ℤ ℤ (S 1), bd I 0 b = c) ∧
  ∀ n, ∀ c ∈ Finsupp.supported ℤ ℤ (S (n + 1)), bd I n c = 0 →
    ∃ b ∈ Finsupp.supported ℤ ℤ (S (n + 2)), bd I (n + 1) b = c

def nerve {I F : Type*} (X : Set F) (A : I → Set F) (n : ℕ) : Set (Fin n → I) :=
  {t | ∃ x ∈ X, ∀ j, x ∈ A (t j)}

theorem nerve_faceClosed {I F : Type*} (X : Set F) (A : I → Set F) : FaceClosed (nerve X A) := by
  intro n t ht j
  obtain ⟨x, hx, hA⟩ := ht
  exact ⟨x, hx, fun i => hA (j.succAbove i)⟩

section Poly

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def poly (q : Y → E →L[ℝ] ℝ) : Set E := {h | ∀ y, 1 ≤ q y h}

def LocFin (q : Y → E →L[ℝ] ℝ) : Prop :=
  ∀ h ∈ poly q, ∃ S : Set Y, S.Finite ∧ ∀ᶠ h' in nhds h, ∀ y ∉ S, 1 < q y h'

def IsVert (q : Y → E →L[ℝ] ℝ) (h : E) : Prop :=
  h ∈ poly q ∧ ∀ k : E, (∀ y, q y h = 1 → q y k = 0) → k = 0

abbrev Vert (q : Y → E →L[ℝ] ℝ) := {h : E // IsVert q h}

def posDual (T : Set E) : Set (E →L[ℝ] ℝ) := {x | ∀ k ∈ T, k ≠ 0 → 0 < x k}

def normalCone (q : Y → E →L[ℝ] ℝ) (h : E) : Set (E →L[ℝ] ℝ) :=
  {x | ∀ h' ∈ poly q, x h ≤ x h'}

def simp (q : Y → E →L[ℝ] ℝ) (T : Set E) (n : ℕ) : Set (Fin n → Vert q) :=
  nerve (posDual T) (fun v : Vert q => normalCone q v.1) n

structure Good (q : Y → E →L[ℝ] ℝ) (T : Set E) : Prop where
  locFin : LocFin q
  nonempty : (poly q).Nonempty
  closed : IsClosed T
  smul_mem : ∀ c : ℝ, 0 < c → ∀ k ∈ T, c • k ∈ T
  sub : poly q ⊆ T
  pos : (posDual T).Nonempty

end Poly

end UpperTheory.V.ConeExtensionAcyclic
