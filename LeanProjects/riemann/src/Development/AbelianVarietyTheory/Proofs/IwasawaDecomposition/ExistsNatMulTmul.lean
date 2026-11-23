import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemMaximalIdealBall
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.MatchCoord (valF_mul valF_res valF_appLE valF_one' valF_eq)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct

namespace GlobalTheory.GenBd

section Norm

variable {C : Type} [NormedField C] [IsUltrametricDist C]

end Norm

theorem norm_valF_le_one {X : Scheme.{0}} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (z : Sp ↥(intO C) ⟶ X) (U : X.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (b : Γ(X, U)) :
    ‖valF (spMap (intO C).subtype ≫ z) U b‖ ≤ 1 := by
  have h' : ⊤ ≤ (spMap (intO C).subtype ≫ z) ⁻¹ᵁ U := fun x _ => h (Set.mem_univ _)
  let ev : Γ(X, U) →+* ↥(intO C) := (Scheme.ΓSpecIso (CommRingCat.of ↥(intO C))).hom.hom.comp (z.appLE U ⊤ h).hom
  have e : ∀ a, valF (spMap (intO C).subtype ≫ z) U a = (ev a : C) := fun a => by
    rw [valF, dif_pos h']
    have e1 : (spMap (intO C).subtype ≫ z).appLE U ⊤ h' = z.appLE U ⊤ h ≫ (spMap (intO C).subtype).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE (spMap (intO C).subtype) z U ⊤ ⊤ h le_top).symm
    rw [e1]
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (intO C).subtype)) _
  rw [e]
  exact (ev b).2

section Charts

variable {X Q : Scheme.{0}} {D : LB X} {ι : Q ⟶ X}

end Charts

end GlobalTheory.GenBd
