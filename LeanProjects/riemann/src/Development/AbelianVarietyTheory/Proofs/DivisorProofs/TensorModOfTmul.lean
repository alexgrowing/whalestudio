import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

variable {R' : Type} [CommRing R'] {I : Ideal R'} {S : Scheme.{0}}

def crysAct (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) : O →+* Module.End R' (Crys κ t A) :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; push κ t (a.act x)
      map_one' := haveI := a.hom 1; (push_congr κ t a.one).trans (push_id κ t)
      map_mul' x y := by
        haveI := a.hom
        exact (push_congr κ t (a.mul x y)).trans (push_comp κ t _ _) }
    fun x y ↦ by
      haveI := a.hom
      haveI : IsMonHom (a.act x * a.act y) := a.add x y ▸ a.hom _
      exact (push_congr κ t (a.add x y)).trans (push_mul κ t _ _)

theorem crysAct_apply (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) (x : O) (h : Crys κ t A) :
    crysAct κ t a x h = (haveI := a.hom x; push κ t (a.act x) h) := rfl

@[reducible] def tensorModOf {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) : Module (C ⊗[ℤ] B) H :=
  Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId C (Module.End C H)) ρ.toIntAlgHom
    fun r _ ↦ Algebra.commutes r _).toRingHom

theorem tensorModOf_tmul {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) (r : C) (x : B) (h : H) :
    (letI := tensorModOf ρ; (r ⊗ₜ[ℤ] x : C ⊗[ℤ] B) • h) = r • ρ x h := rfl

end GlobalTheory.HTSummand
