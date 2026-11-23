import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDim

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem isMonHom_mul_of_isCommMonObj {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) where
  one_hom := by
    rw [Hom.mul_def]
    exact IsMonHom.one_hom _
  mul_hom := by
    rw [Hom.mul_def]
    exact IsMonHom.mul_hom _

theorem exists_oAct_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (O : Type) [CommRing O] (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (r : O →+* Module.End ℂ (Fin P.g → ℂ)), (∀ a, ∀ z ∈ u.Λ, r a z ∈ u.Λ) → ∃ act : OAct O P.A, ∀ a z, u.ex (r a z) = u.ex z ≫ act.act a := by
  intro hL hL2 hGen hTh O _ P u r hr

  have key : ∀ a, ∃! f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (r a z) = u.ex z ≫ f := fun a =>
    existsUnique_isMonHom_of_map_lattice hL hL2 hGen hTh P P P.L P.L u u (r a) (hr a)
  choose act hact huniq using key
  have eq_of : ∀ a (h : P.A ⟶ P.A), IsMonHom h → (∀ z, u.ex (r a z) = u.ex z ≫ h) → h = act a :=
    fun a h h1 h2 => huniq a h ⟨h1, h2⟩
  have hom : ∀ a, IsMonHom (act a) := fun a => (hact a).1
  refine ⟨⟨act, hom, ?_, ?_, ?_⟩, fun a z => (hact a).2 z⟩
  · refine (eq_of 1 (𝟙 _) inferInstance ?_).symm
    intro z
    simp
  · intro a b
    refine (eq_of (a * b) (act a ≫ act b) inferInstance ?_).symm
    intro z
    rw [mul_comm a b, map_mul, Module.End.mul_apply, (hact b).2, (hact a).2, Category.assoc]
  · intro a b
    have := hom a
    have := hom b
    refine (eq_of (a + b) (act a * act b) (isMonHom_mul_of_isCommMonObj _ _) ?_).symm
    intro z

    rw [map_add, LinearMap.add_apply, u.2, (hact a).2, (hact b).2, MonObj.comp_mul]

end GlobalTheory
