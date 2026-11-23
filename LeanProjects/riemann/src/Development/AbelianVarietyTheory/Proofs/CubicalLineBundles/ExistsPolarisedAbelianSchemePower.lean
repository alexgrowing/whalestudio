import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxPowerBasic
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmplePowObjBoxLB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CM

theorem exists_polAV_isPowGrp : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ), ∃ (Q : Out.PolAV (Sp R)) (_ : Out.IsPowGrp Q.A P.A n), Q.g = n * P.g := by
  intro R _ P n
  have := P.isAb.comm
  obtain ⟨hL, hS, hr⟩ := BoxPower.boxPower_basic R P n
  obtain ⟨rig, hrig⟩ := P.rigid
  exact ⟨{ A := Out.powObj P.A n
           isAb := (PowGrp.powers _ _ _ n (Out.powIsPowGrp P.A n)).2.2.2.1 P.isAb
           g := n * P.g
           smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ n P.smoothDim
           L := Out.boxLB P.L (Out.powPr P.A (n := n))
           isLB := hL
           rigid := ⟨_, hr rig hrig⟩
           sym := hS
           ample := relAmple_powObj_boxLB R P n
           ktriv := kTriv_boxLB _ (Out.powObj P.A n) P.A n (Out.powIsPowGrp P.A n) P.L P.isLB P.ktriv },
    Out.powIsPowGrp P.A n, rfl⟩

end GlobalTheory.CM
