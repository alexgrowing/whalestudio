import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusCoord

theorem val_torus_point_and_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Geo.Tor.Good D.P.L z J → ∀ χ : D.X, Geo.Tor.val (g.t χ) (τ ≫ g.i).left z J = Geo.Tor.gm τ.left z ⊤ (charUnit _ D.X χ) ∧ Geo.Tor.val (g.t χ) ((τ ≫ g.i) * y).left z J = Geo.Tor.gm τ.left z ⊤ (charUnit _ D.X χ) * Geo.Tor.val (g.t χ) y.left z J := by
  intro R _ _ I D e G _ _ g Z τ y z J hJ χ
  refine ⟨?_, GlobalTheory.TorusCoord.val_torus g χ hJ τ y⟩
  rw [GlobalTheory.TorusCoord.val_congr g χ (_root_.mul_one (τ ≫ g.i)).symm z J, GlobalTheory.TorusCoord.val_torus g χ hJ τ 1,
    GlobalTheory.TorusCoord.val_unit g χ hJ, _root_.mul_one]

end GlobalTheory.TorusCoord
