import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_eighthPower_semiAbelianScheme : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∃ (G₈ : Over (Sp R)) (_ : GrpObj G₈) (prG : Fin 8 → (G₈ ⟶ G)), IsSemiAbelian G₈ ∧ (∀ u, IsMonHom (prG u)) ∧ ∀ (T : Over (Sp R)) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ G₈, ∀ u, x ≫ prG u = y u := by
  intro R _ G _ hG
  haveI : IsCommMonObj G := hG.comm
  refine ⟨powObj G 8, inferInstance, powPr G, ?_, fun u => inferInstance, fun T y => ?_⟩
  · exact GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G 8) G 8 (powIsPowGrp G 8) hG
  · refine ⟨(powIsLimit G 8).lift (Fan.mk T y), fun u => (powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩, ?_⟩
    intro x hx
    apply (powIsLimit G 8).hom_ext
    rintro ⟨u⟩
    exact (hx u).trans ((powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩).symm

end GlobalTheory.MBLow
