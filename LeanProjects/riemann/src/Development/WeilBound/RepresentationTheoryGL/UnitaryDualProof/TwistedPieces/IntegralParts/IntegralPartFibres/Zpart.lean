import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.TranslInv

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def CC (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k) := ZN Z ∩ Bz Z

open Classical in

def zpart (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k :=
  if h : ∃ c ∈ Z, IsNilpotent (x - c) then h.choose else 0

structure IsLat (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (L : AddSubgroup (Matrix (Fin n) (Fin n) k)) : Prop where
  sub : (L : Set (Matrix (Fin n) (Fin n) k)) ⊆ Z
  cpt : IsCompact (L : Set (Matrix (Fin n) (Fin n) k))
  nhd : ∃ U : Set (Matrix (Fin n) (Fin n) k), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) k) ∈ U ∧ U ∩ Z ⊆ L
  int : ∀ a : k, ValuativeRel.valuation k a ≤ 1 → ∀ x ∈ L, a • x ∈ L

end PositivityTheory.RgUd.TP.Nil.Fib1
