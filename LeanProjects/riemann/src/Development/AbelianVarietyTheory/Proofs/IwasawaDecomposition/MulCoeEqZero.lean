import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpUniqCh0

section Alg

variable {S A : Type} [CommRing S] [CommRing A] [Algebra S A] (J : Ideal A) [Module Sᵐᵒᵖ J] [IsCentralScalar S J]

theorem mul_coe_eq_zero (hJ : J ^ 2 = ⊥) (a b : J) : (a : A) * (b : A) = 0 := by
  have h : (a : A) * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul a.2 b.2
  rw [hJ] at h
  exact h

def incl (hJ : J ^ 2 = ⊥) : TrivSqZeroExt S J →ₐ[S] A where
  toFun x := algebraMap S A x.fst + (x.snd : A)
  map_one' := by simp
  map_mul' x y := by
    have h := mul_coe_eq_zero J hJ x.snd y.snd
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, map_mul, Submodule.coe_add, op_smul_eq_smul,
      Submodule.coe_smul_of_tower, Algebra.smul_def]
    linear_combination (-1 : A) * h
  map_zero' := by simp
  map_add' x y := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add, Submodule.coe_add]; ring
  commutes' s := by simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem incl_apply (hJ : J ^ 2 = ⊥) (x : TrivSqZeroExt S J) : incl J hJ x = algebraMap S A x.fst + (x.snd : A) := rfl

end Alg

variable {S : Type} [CommRing S] {ρ : Type}

def diag (m : ℕ) : Jet S (Fin 2 × ρ) m →ₐ[S] Jet S ρ m :=
  jetMap (fun p => MvPolynomial.X p.2) fun p => X_mem_orig p.2

end GlobalTheory.ExpUniqCh0
