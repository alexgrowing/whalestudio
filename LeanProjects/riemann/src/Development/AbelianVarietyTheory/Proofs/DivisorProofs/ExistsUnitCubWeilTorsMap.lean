import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_unit_cubWeil_torsMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (N : ℕ) (B : Type) [CommRing B] [Algebra R B] (z z' : Tors t.G N B), ∃ ζ : Bˣ, ∀ (C : Type) [CommRing C] [Algebra R C] (ψ : B →ₐ[R] C), GlobalTheory.UU.CubWeil t.cub N (torsMap ψ z).1 (torsMap ψ z').1 (unitOn (Units.map (ψ : B →* C) ζ)) := by
  intro E _ _ _ H R _ t N B _ _ z z'
  obtain ⟨e, he, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t.cub z.2 z'.2
  refine ⟨Units.map ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom : Γ(Sp B, ⊤) →* B) e, fun C _ _ ψ => ?_⟩
  have h := he.comp (spOver ψ)
  have k : unitOn (Units.map (ψ : B →* C)
      (Units.map ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom : Γ(Sp B, ⊤) →* B) e)) =
      Units.map (spOver ψ).left.appTop.hom.toMonoidHom e := by
    apply Units.ext
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (ψ : B →+* C))
    have n' : (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom (ψ : B →+* C) ≫
        (Scheme.ΓSpecIso (CommRingCat.of C)).inv = (Spec.map (CommRingCat.ofHom (ψ : B →+* C))).appTop := by
      rw [← Category.assoc, ← n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact congrArg (fun q => q.hom e.val) n'
  rw [k]
  exact h

end GlobalTheory.GroupBplus.Aff
