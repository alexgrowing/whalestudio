import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE

theorem secs_map_arrow {X : Scheme.{0}} {E : X.Modules} (D : Subobject E)
    (B : Subobject (D : X.Modules)) (V : X.Opens) :
    secs ((Subobject.map D.arrow).obj B) V = (D.arrow.app V) '' secs B V := by
  have hmk : (Subobject.map D.arrow).obj B = Subobject.mk (B.arrow ≫ D.arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow B]
    exact Subobject.map_mk _ _
  let e := Subobject.isoOfEqMk _ _ hmk
  have he : e.hom ≫ (B.arrow ≫ D.arrow) = ((Subobject.map D.arrow).obj B).arrow := by
    simp only [e, Subobject.isoOfEqMk_hom, Subobject.ofLEMk_comp]
  have he' : e.inv ≫ ((Subobject.map D.arrow).obj B).arrow = B.arrow ≫ D.arrow := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  ext y
  simp only [GlobalTheory.CompanionTheory.GE.secs]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(B.arrow.app V) ((e.hom.app V) x), ⟨_, rfl⟩, ?_⟩
    have h := congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) x) he
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(e.inv.app V) x, ?_⟩
    have h := congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) x) he'
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h

end GlobalTheory.CompanionTheory.GE
