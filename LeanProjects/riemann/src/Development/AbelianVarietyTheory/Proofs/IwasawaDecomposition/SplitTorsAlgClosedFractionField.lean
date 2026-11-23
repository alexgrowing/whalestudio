import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionFlatLocallyQuasiFiniteStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm

theorem splitTors_of_isAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsAlgClosed (FractionRing R)] (x : Sp R ⟶ X) (q : ℕ), q ≠ 0 → SplitTors t x q := by
  intro E _ _ _ H X _ t R _ _ _ x q hq Ω _ io w hw
  have hqf : LocallyQuasiFinite (torsion t.G q).hom := (GlobalTheory.T.torsion_flat_locallyQuasiFinite X t.G t.semi q hq).2
  let _ : Algebra (FractionRing R) Ω := io.toAlgebra
  have hic : IsIntegrallyClosedIn (FractionRing R) Ω := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨io.injective, fun {z} hz => ?_⟩
    exact (minpoly.degree_eq_one_iff.mp (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hz)))
  let l := GlobalTheory.KernelNoTorsion.torsionLift w hw
  have hl : l ≫ torsion.ι t.G q = w := GlobalTheory.KernelNoTorsion.torsionLift_ι w hw
  obtain ⟨x₀, h₀, -⟩ := GlobalTheory.OnePoint.exists_point_of_locallyQuasiFinite (K := FractionRing R) (torsion t.G q).hom Ω l.left
    (spMap (algebraMap R (FractionRing R)) ≫ x) (by
      rw [Over.w l]
      change spMap _ ≫ x = spMap io ≫ spMap _ ≫ x
      rw [← Category.assoc, ← Spec.map_comp]
      rfl)
  refine ⟨x₀ ≫ (torsion.ι t.G q).left, ?_⟩
  rw [← hl, Over.comp_left, ← h₀, Category.assoc]

end GlobalTheory.LineNorm
