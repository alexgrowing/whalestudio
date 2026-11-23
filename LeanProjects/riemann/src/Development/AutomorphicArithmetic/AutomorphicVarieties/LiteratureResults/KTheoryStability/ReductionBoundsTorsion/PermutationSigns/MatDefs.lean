import Mathlib

noncomputable section

open Matrix

namespace PositivityTheory.KB.BlockInvariants

abbrev Ix (W : Type) (m : ℕ) : Type := W × Fin m

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

def blk (d : W → Matrix (Fin m) (Fin m) ℂ) : Matrix (Ix W m) (Ix W m) ℂ :=
  Matrix.of fun x y => if x.1 = y.1 then d x.1 x.2 y.2 else 0

def tp {ι : Type} (q : ℕ) (M : Matrix ι ι ℂ) : Matrix (Fin q → ι) (Fin q → ι) ℂ :=
  Matrix.of fun I J => ∏ i, M (I i) (J i)

def perm' (σ : Equiv.Perm (Fin q)) (w : Fin q → W) : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ :=
  Matrix.of fun I J => if (∀ i, (I i).1 = w i) ∧ J = I ∘ σ then 1 else 0

def PlacePermOperatorBicommutantSpan : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (m q : ℕ) (T : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ),
    (∀ Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ,
      (∀ (σ : Equiv.Perm (Fin q)) (w : Fin q → W), Z * perm' σ w = perm' σ w * Z) → T * Z = Z * T) →
    T ∈ Submodule.span ℂ (Set.range fun p : Equiv.Perm (Fin q) × (Fin q → W) => (perm' (m := m) p.1 p.2))

def PlacePermOperatorCommutantSpan : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (m q : ℕ) (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ),
    (∀ (σ : Equiv.Perm (Fin q)) (w : Fin q → W), Z * perm' σ w = perm' σ w * Z) →
    Z ∈ Submodule.span ℂ {M | ∃ d : W → Matrix (Fin m) (Fin m) ℂ,
      (∀ w, d w ∈ Matrix.unitaryGroup (Fin m) ℂ) ∧ M = tp q (blk d)}

end PositivityTheory.KB.BlockInvariants

end
