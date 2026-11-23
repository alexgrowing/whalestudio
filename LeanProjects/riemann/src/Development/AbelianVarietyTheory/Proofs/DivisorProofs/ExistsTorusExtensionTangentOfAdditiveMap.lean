import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorVec

theorem exists_torus_tangent : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ D l
  obtain ⟨ν, hb, hv⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := epsR R)
    (fun x => GlobalTheory.TorusTangent.oneAdd (l x)) fun x y => by rw [map_add, GlobalTheory.TorusTangent.oneAdd_add]
  refine ⟨ν, ?_, hb, fun χ Z q z J hJ => ?_⟩
  · obtain ⟨g₀, h₀, v₀⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := baseOver (Sp R)) (fun _ => 1)
      fun _ _ => (_root_.mul_one _).symm
    refine ⟨g₀, ⟨h₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩, ?_, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [v₀ x _ _ y J hJ, map_one, val_one]
    · rw [h₀, hb, GlobalTheory.TorusTangent.zeroT_left, GlobalTheory.TorusTangent.zeroT_left, ← Category.assoc]
      exact congrArg (· ≫ eSec D.P.A) GlobalTheory.TorusTangent.fst_inl.symm
    · refine (v₀ x _ _ y J hJ).trans (Units.ext (Eq.trans ?_
        (GlobalTheory.TorusTangent.hasVal_spMap (hv x) (TrivSqZeroExt.fstHom R R R).toRingHom hJ).symm))
      rw [GlobalTheory.TorusTangent.valR_oneAdd, map_one]
      simp
  · rw [hv χ Z q z J hJ, ← gs_unit q z ⊤ trivial]
    rfl

end GlobalTheory.MBLow.TorVec

end
