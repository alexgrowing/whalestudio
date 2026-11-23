import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovLift

theorem exists_lift_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] (W Y : Scheme.{0}) [IsIntegral W]
    (π : W ⟶ Y) [IsFinite π] (y : Spec (CommRingCat.of K) ⟶ Y)
    (h : π (genericPoint W) ⤳ y (IsLocalRing.closedPoint K)) :
    ∃ w : Spec (CommRingCat.of K) ⟶ W, w ≫ π = y := by
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  obtain ⟨w₀, hw₀⟩ : y (IsLocalRing.closedPoint K) ∈ Set.range π :=
    h.mem_closed hcl ⟨_, rfl⟩
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective y
  have hy : (Scheme.SpecToEquivOfField K Y).symm ⟨p, φ⟩ =
      Spec.map φ ≫ Y.fromSpecResidueField p := rfl
  rw [hy] at hw₀ ⊢
  have hp : π w₀ = p := by
    rw [hw₀]
    exact Scheme.fromSpecResidueField_apply p (Spec.map φ (IsLocalRing.closedPoint K))
  subst hp
  have hfin : (π.residueFieldMap w₀).hom.Finite := residueFieldMap_finite_of_locallyQuasiFinite π w₀
  letI : Algebra (Y.residueField (π w₀)) (W.residueField w₀) := (π.residueFieldMap w₀).hom.toAlgebra
  letI : Algebra (Y.residueField (π w₀)) K := φ.hom.toAlgebra
  haveI : Module.Finite (Y.residueField (π w₀)) (W.residueField w₀) := hfin
  let ψ : W.residueField w₀ →ₐ[Y.residueField (π w₀)] K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ W.fromSpecResidueField w₀, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext a
  exact ψ.commutes a

theorem exists_lift_of_specializes : ∀ (W Y : Scheme.{0}) [IsIntegral W] (π : W ⟶ Y), IsFinite π → ∀ y : Sp Qb ⟶ Y, π (genericPoint W) ⤳ y (IsLocalRing.closedPoint Qb) → ∃ w : Sp Qb ⟶ W, w ≫ π = y := by
  intro W Y _ π hπ y h
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  exact exists_lift_of_isAlgClosed Qb W Y π y h

end GlobalTheory.CovLift
