import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module

variable {F : Type} [Field F] {r : ℕ}

def colSet (F : Type) [Field F] (b : Fin r → ℕ) (k : ℕ) : Set (blockTri (κ := F) b) :=
  {p | (p : GL (Fin r) F) ∈ unip F r ∧ ∀ i j : Fin r, j.val < k →
    ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j}

def colChar (ψ : AddChar F ℂ) (b : Fin r → ℕ) (k : Fin r) (l : Fin r → F) (p : blockTri (κ := F) b) : ℂ :=
  ψ (∑ i, l i * ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k +
    edgeSum (fun i j => blkEdge b i j ∧ k < j) (p : GL (Fin r) F))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ : G → ℂ) (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem eig_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ χ' : G → ℂ) (h : ∀ g ∈ S, χ g = χ' g) : eig τ S χ = eig τ S χ' := by
  ext v
  simp only [mem_eig]
  exact forall₂_congr fun g hg => by rw [h g hg]

end GlobalTheory.FinGL.LeviWh
