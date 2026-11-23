import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.ColumnForm

section Sets

variable (k : Type) [Field k]

def colSet (N m : ℕ) : Set (GL (Fin N) k) :=
  {u | ∀ i j : Fin N, (j ≤ i ∨ (j : ℕ) < m) → u.val i j = (1 : Matrix (Fin N) (Fin N) k) i j}

def cornerSet (N m : ℕ) : Set (GL (Fin N) k) :=
  {g | ∀ i j : Fin N, (m ≤ (i : ℕ) + 1 ∨ m ≤ (j : ℕ)) → g.val i j = (1 : Matrix (Fin N) (Fin N) k) i j}

variable {k}

def colSum {N : ℕ} (l : ℕ) (u : GL (Fin N) k) : k :=
  ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ l ≤ (p.2 : ℕ), u.val p.1 p.2

def headScalar (a b : ℕ) (t : kˣ) : GL (Fin (a + b)) k :=
  emb₂ k (stdSum (rfl : a + b = a + b)) (Matrix.GeneralLinearGroup.scalar (Fin a) t, 1)

theorem one_mem (N m : ℕ) : (1 : GL (Fin N) k) ∈ colSet k N m ∧ (1 : GL (Fin N) k) ∈ cornerSet k N m :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end Sets

variable {k : Type} [Field k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

def colKer (π : Representation ℂ (GL (Fin N) k) V) (ψ : AddChar k Circle) (m l : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ u ∈ colSet k N m, ∃ v, w = π u v - (ψ (colSum l u) : ℂ) • v}

def IsPosForm (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ ∀ v, 0 ≤ (B v v).re

def IsHermPair {G : Type} [Group G] (π : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ, (∀ g v w, C (π g v) (σ g w) = C v w) ∧ (∀ v, (∀ w, C v w = 0) → v = 0) ∧
    ∀ w, (∀ v, C v w = 0) → w = 0

theorem isHermPair_self {G : Type} [Group G] {π : Representation ℂ G V} (h : IsUnitarisable π) : IsHermPair π π := by
  obtain ⟨B, -, h2, h3⟩ := h
  refine ⟨B, h3, fun v hv => ?_, fun v hv => ?_⟩ <;>
  · by_contra h0
    have := h2 v h0
    rw [hv v] at this
    simp at this

def IsAvg {X : Type} [AddCommGroup X] (u : Representation ℂ (Multiplicative X) V) (L : AddSubgroup X) (χ : L → ℂ)
    (E : Module.End ℂ V) : Prop :=
  (∀ (x : L) v, u (Multiplicative.ofAdd (x : X)) (E v) = χ x • E v) ∧
    (∀ (x : L) v, E (u (Multiplicative.ofAdd (x : X)) v) = χ x • E v) ∧
    ∀ v, v - E v ∈ Submodule.span ℂ {w | ∃ (x : L) (y : V), w = u (Multiplicative.ofAdd (x : X)) y - χ x • y}

theorem isAvg_bot {X : Type} [AddCommGroup X] (u : Representation ℂ (Multiplicative X) V) :
    IsAvg u ⊥ (fun _ => 1) 1 := by
  have h : ∀ (x : (⊥ : AddSubgroup X)) v, u (Multiplicative.ofAdd (x : X)) v = v := fun x v => by
    rw [AddSubgroup.mem_bot.1 x.2]; simp
  exact ⟨fun x v => by simp [h], fun x v => by simp [h], fun v => by simp⟩

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def HasColumnForm (π : Representation ℂ (GL (Fin N) k) V) (ψ : AddChar k Circle) (m : ℕ) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsPosForm B ∧ (∀ v, B v v = 0 ↔ v ∈ colKer π ψ m m) ∧
    ∀ g ∈ cornerSet k N m, ∀ v w, B (π g v) (π g w) =
      ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g) ^ (N - m) : ℝ) : ℂ) * B v w

end GlobalTheory.ColumnForm

end
