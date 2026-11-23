import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

namespace GlobalTheory.FlagCls

theorem finite_exists_lift_algClosed_point : ∀ (Bg S : Scheme.{0}) (πB : Bg ⟶ S), IsFinite πB → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), x (IsLocalRing.closedPoint K) ∈ Set.range πB → ∃ xb : Sp K ⟶ Bg, xb ≫ πB = x := by
  intro Bg S πB hfin K _ _ x hx
  obtain ⟨b, hb⟩ := hx
  obtain ⟨⟨s, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K S).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hb
  have hs : (Spec.map φ ≫ S.fromSpecResidueField s) (IsLocalRing.closedPoint K) = s := by
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Function.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  rw [hs] at hb
  subst hb
  letI : Algebra (S.residueField (πB b)) (Bg.residueField b) := (πB.residueFieldMap b).hom.toAlgebra
  haveI : Module.Finite (S.residueField (πB b)) (Bg.residueField b) :=
    GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite πB b
  haveI : Algebra.IsAlgebraic (S.residueField (πB b)) (Bg.residueField b) :=
    Algebra.IsAlgebraic.of_finite _ _
  letI : Algebra (S.residueField (πB b)) K := φ.hom.toAlgebra
  let ψ : Bg.residueField b →ₐ[S.residueField (πB b)] K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Bg.fromSpecResidueField b, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp]
  simp only [Scheme.SpecToEquivOfField_symm_apply]
  congr 2
  ext c
  exact ψ.commutes c

end GlobalTheory.FlagCls
