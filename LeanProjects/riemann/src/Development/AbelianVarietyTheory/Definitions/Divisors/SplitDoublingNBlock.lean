import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup

noncomputable section

namespace GlobalTheory.FinGL

open Formalism.L2.DIV Module

def eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ) :
    Submodule ℂ V :=
  ⨅ g ∈ S, LinearMap.ker (τ g - χ g • LinearMap.id)

variable {F : Type} [Field F] {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def whDim (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) : ℕ :=
  finrank ℂ (eig τ (unip F r : Set (GL (Fin r) F)) fun g => ψ (edgeSum supEdge g))

def cutEdge (j : ℕ) (a b : Fin r) : Prop := b.val = a.val + 1 ∧ a.val + 1 ≠ j

instance (j : ℕ) : DecidableRel (cutEdge (r := r) j) := fun a b =>
  inferInstanceAs (Decidable (b.val = a.val + 1 ∧ a.val + 1 ≠ j))

def whCut (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) (j : ℕ) : ℕ :=
  finrank ℂ (eig τ (unip F r : Set (GL (Fin r) F)) fun g => ψ (edgeSum (cutEdge j) g))

def nPos (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) (ρ k : ℕ) : ℕ :=
  finrank ℂ (eig τ (unipSym F r ρ k : Set (GL (Fin r) F)) fun g => ψ (edgeSum (symEdge ρ k) g))

def gam (q l : ℕ) : ℕ := if l = 0 then 1 else q ^ l - q ^ (l - 1)

def splitDoublingNBlock (b : Fin r → ℕ) (j : ℕ) : ℕ :=
  ((Finset.univ.image b).powerset.filter fun J => (Finset.univ.filter fun i => b i ∈ J).card = j).card

structure IsCuspDatum (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) : Prop where
  mono : Monotone b
  irr : σ.IsIrreducible
  infl : ∀ p : blockTri (κ := F) b, (∀ i j, b i = b j →
    ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1
  cusp : ∀ S : Finset (Fin r), (∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : V,
    (∀ u : blockTri (κ := F) b, (∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S) → σ u y = y) → y = 0

abbrev parInd (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) :=
  Representation.coind (blockTri (κ := F) b).subtype σ

def blkEdge (b : Fin r → ℕ) (i j : Fin r) : Prop := j.val = i.val + 1 ∧ b i = b j

instance (b : Fin r → ℕ) : DecidableRel (blkEdge b) := fun i j =>
  inferInstanceAs (Decidable (j.val = i.val + 1 ∧ b i = b j))

def leviWh (ψ : AddChar F ℂ) (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) : ℕ :=
  finrank ℂ (eig σ {p | (p : GL (Fin r) F) ∈ unip F r} fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F)))

end GlobalTheory.FinGL
