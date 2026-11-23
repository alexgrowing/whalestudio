import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.GroupBplus

namespace GlobalTheory.BplusDescent

variable {X : Scheme.{0}} [IsIntegral X]

def ringOver (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) : Subring U.Bp :=
  K'.toSubalgebra.toSubring.comap (algebraMap U.Bp (Kbar X))

theorem mem_ringOver {K' : IntermediateField X.functionField (Kbar X)} {U : AffOp X} {x : U.Bp} :
    x ∈ ringOver K' U ↔ (x : Kbar X) ∈ K' := Iff.rfl

def descMod (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) {h : ℕ}
    (L : Submodule U.Bp (Fin h → U.Bp)) : Submodule (ringOver K' U) (Fin h → ringOver K' U) where
  carrier := {a | (fun i => (a i : U.Bp)) ∈ L}
  add_mem' {a b} ha hb := by
    have : (fun i => ((a + b) i : U.Bp)) = (fun i => (a i : U.Bp)) + fun i => (b i : U.Bp) := by
      funext i; simp
    change (fun i => ((a + b) i : U.Bp)) ∈ L
    rw [this]; exact L.add_mem ha hb
  zero_mem' := by
    have : (fun i => ((0 : Fin h → ringOver K' U) i : U.Bp)) = 0 := by funext i; simp
    change (fun i => ((0 : Fin h → ringOver K' U) i : U.Bp)) ∈ L
    rw [this]; exact L.zero_mem
  smul_mem' c a ha := by
    have : (fun i => ((c • a) i : U.Bp)) = (c : U.Bp) • fun i => (a i : U.Bp) := by
      funext i; simp
    change (fun i => ((c • a) i : U.Bp)) ∈ L
    rw [this]; exact L.smul_mem (c : U.Bp) ha

theorem mem_descMod {K' : IntermediateField X.functionField (Kbar X)} {U : AffOp X} {h : ℕ}
    {L : Submodule U.Bp (Fin h → U.Bp)} {a : Fin h → ringOver K' U} :
    a ∈ descMod K' U L ↔ (fun i => (a i : U.Bp)) ∈ L := Iff.rfl

def IsDescended (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) {h : ℕ}
    (L : Submodule U.Bp (Fin h → U.Bp)) : Prop :=
  Module.Finite (ringOver K' U) (descMod K' U L) ∧ Module.Projective (ringOver K' U) (descMod K' U L) ∧
    L = Submodule.span U.Bp {x | ∃ a ∈ descMod K' U L, x = fun i => (a i : U.Bp)}

end GlobalTheory.BplusDescent
