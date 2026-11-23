import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.SecTransport

theorem main : ∀ {X : Scheme.{0}} {M L : LB X} (e : LB.Iso M L), e.IsGen → M.IsLB → L.IsLB →
    ∀ σ : L.Sec, ∃ σ' : M.Sec, GlobalTheory.Cartier.SecMaps e σ' σ ∧ Out.nonzeroLocus σ ≤ Out.nonzeroLocus σ' := by
  intro X M L e he hM hL σ
  refine ⟨DVR.secOfIso (u := e) σ he hM hL, ?_, DVR.nonzeroLocus_secOfIso e σ he hM hL⟩
  intro p
  apply GlobalTheory.Cartier.ext_germ
  intro x hx
  set σ' := DVR.secOfIso (u := e) σ he hM hL
  have hx' : x ∈ M.U p.2 ⊓ L.U p.1 := ⟨hx.2, hx.1⟩
  have h1 : (X.presheaf.germ _ x hx).hom (resG X (inf_le_left : L.U p.1 ⊓ M.U p.2 ≤ L.U p.1) (σ.f p.1)) =
      (X.presheaf.germ _ x hx.1).hom (σ.f p.1) := GlobalTheory.Cartier.germ_resG _ x hx _
  have h2 : (X.presheaf.germ _ x hx).hom (resG X (inf_le_right : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2) (σ'.f p.2)) =
      (X.presheaf.germ _ x hx.2).hom (σ'.f p.2) := GlobalTheory.Cartier.germ_resG _ x hx _
  have h3 : (X.presheaf.germ _ x hx.2).hom (σ'.f p.2) =
      (X.presheaf.germ _ x hx').hom (DVR.isoCand e σ p.2 p.1) := by
    rw [← DVR.secOfIso_spec (u := e) σ he hM hL p.2 p.1]
    exact (GlobalTheory.Cartier.germ_resG (inf_le_left : M.U p.2 ⊓ L.U p.1 ≤ M.U p.2) x hx' _).symm
  have h4 : (X.presheaf.germ _ x hx').hom (DVR.isoCand e σ p.2 p.1) =
      (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p))⁻¹ : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) *
        (X.presheaf.germ _ x hx.1).hom (σ.f p.1) := by
    unfold DVR.isoCand
    rw [map_mul]
    congr 1
    exact GlobalTheory.Cartier.germ_resG (inf_le_right : M.U p.2 ⊓ L.U p.1 ≤ L.U p.1) x hx' _
  have h5 : (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p)) : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) =
      (X.presheaf.germ _ x hx).hom ((@id (Γ(X, L.U p.1 ⊓ M.U p.2)ˣ) (e.s p) : Γ(X, L.U p.1 ⊓ M.U p.2))) :=
    GlobalTheory.Cartier.germ_resG (DVR.divLe p.2 p.1) x hx' _
  have h6 : (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p)) : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) *
      (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p))⁻¹ : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul, h1, h2, h3, h4, ← h5, ← _root_.mul_assoc, h6, _root_.one_mul]

end GlobalTheory.SecTransport
