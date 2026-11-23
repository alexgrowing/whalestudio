import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

def ptE (t : E) (x : Fin 2 → maximalRealSubfield E) : E := ((x 0 : maximalRealSubfield E) : E) * t + ((x 1 : maximalRealSubfield E) : E)

theorem ptE_smul (t : E) (a : OF E) (x : Fin 2 → maximalRealSubfield E) :
    ptE t (a • x) = algebraMap (OF E) E a * ptE t x := by
  simp only [ptE, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  push_cast
  have h : (((algebraMap (OF E) (maximalRealSubfield E) a) : maximalRealSubfield E) : E) = algebraMap (OF E) E a := rfl
  rw [h]; ring

def pass (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) : GlobalTheory.HilbFam.Lat (maximalRealSubfield E) where
  carrier := {x | ptE t x ∈ lattice c y}
  add_mem' := fun {x x'} hx hx' => by
    have : ptE t (x + x') = ptE t x + ptE t x' := by simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring
    show ptE t (x + x') ∈ lattice c y
    rw [this]; exact (latticeSub c y).add_mem hx hx'
  zero_mem' := by
    show ptE t 0 ∈ lattice c y
    have : ptE t 0 = 0 := by simp [ptE]
    rw [this]; exact (latticeSub c y).zero_mem
  smul_mem' := fun a x hx => by
    show ptE t (a • x) ∈ lattice c y
    rw [ptE_smul]; exact mul_mem_lattice (algebraMap_mem_orderC c a) hx

theorem mem_pass (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (x : Fin 2 → maximalRealSubfield E) :
    x ∈ pass t c y ↔ ptE t x ∈ lattice c y := Iff.rfl

end GlobalTheory.RoadE
