import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic

namespace PositivityTheory.RgUd.T.Desc.SLT

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Lc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) : Subgroup (GL (Fin n) k) :=
  GzS Z ⊓ GLnLocal.congruenceSubgroup k n m

def IndexSym : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ g ∈ Gz Z, ∃ c : ℕ, ∀ m ≥ c, ∀ m' ≥ m + c,
    Lc Z m' ≤ Lc Z m ⊓ (Lc Z m).map (MulAut.conj g).toMonoidHom ∧
    (Lc Z m').relIndex ((Lc Z m).map (MulAut.conj g).toMonoidHom) = (Lc Z m').relIndex (Lc Z m) ∧
    (Lc Z m').relIndex (Lc Z m) ≠ 0

def OpenSlice : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ (s : Matrix (Fin n) (Fin n) k)
    (F : Set (Matrix (Fin n) (Fin n) k)) (P : k[X]), IsClosed F → F ⊆ Bz Z →
    (∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F) →
    (∀ x ∈ F, aeval x P ∈ F ∧ Module.End.IsSemisimple (Matrix.toLin' (aeval x P)) ∧ IsNilpotent (x - aeval x P) ∧
      ∃ g ∈ Gz Z, g.val * aeval x P * g⁻¹.val = s) →
    ∀ y₀ ∈ F, aeval y₀ P = s → ∀ j : ℕ, ∃ U ∈ nhds y₀, ∀ x ∈ U ∩ F, ∃ l ∈ Lc Z j, aeval (l⁻¹.val * x * l.val) P = s

end PositivityTheory.RgUd.T.Desc.SLT
