import Development.EtaleCohomology.DivisorCycles.OpenCoset
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CosetOfCover

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.OpenCosetPf
open LateralTheory.DivDb

def J {Γ C : Type} [Group Γ] [Field C] {n : ℕ} (r : Γ →* GL (Fin n) C) (S : Set Γ) : Ideal (MP C n) where
  carrier := {q | ∀ x ∈ S, ev (r x : Mat C n) q = 0}
  zero_mem' := fun x _ => by simp [ev]
  add_mem' := fun {a b} ha hb x hx => by
    have h1 := ha x hx; have h2 := hb x hx
    simp only [ev, map_add] at *; rw [h1, h2, add_zero]
  smul_mem' := fun c q hq x hx => by
    have h1 := hq x hx
    simp only [ev, smul_eq_mul, map_mul] at *; rw [h1, mul_zero]

theorem main (hChain : Chain) : OpenCoset :=
  _root_.UpperTheory.Reformulated.B.Qn18.main hChain

end LateralTheory.DivDb.OpenCosetPf

namespace LateralTheory.DivDb
theorem OpenCoset_of (hChain : Chain) : OpenCoset := OpenCosetPf.main hChain
end LateralTheory.DivDb
