import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxPowerBasic
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmplePowObjBoxLB
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KTrivBoxLBPowObj
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow

theorem exists_isKeyPow : ∀ (R : Type) [CommRing R] (x : KeyIn R) (j : ℕ), 1 ≤ j → ∃ y, GlobalTheory.KeyPow.IsKeyPow y x j := by
  intro R _ x j hj
  have := x.P.isAb.comm
  obtain ⟨hL, hS, hr⟩ := BoxPower.boxPower_basic R x.P j
  have hr' := hr x.rig x.rig_gen
  have hA : IsAbelianScheme (Out.powObj x.P.A j) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
    exact AbelianSchemeGerms.isAbelianScheme_powObj x.P.A x.P.isAb n
  let P' : Out.PolAV (Sp R) :=
    { A := Out.powObj x.P.A j
      isAb := hA
      g := j * x.P.g
      smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ j x.P.smoothDim
      L := Out.boxLB x.P.L (Out.powPr x.P.A (n := j))
      isLB := hL
      rigid := ⟨_, hr'⟩
      sym := hS
      ample := relAmple_powObj_boxLB R x.P j
      ktriv := kTriv_boxLB_powObj R x.P j }
  obtain ⟨th, hth, hne⟩ := BoxSection.exists_boxSec _ _ _ j (Out.powIsPowGrp x.P.A j) x.P.L (fun _ => x.th) x.P.isLB
  obtain ⟨v, hv, hvp⟩ := PowLie.isLieBasis_pow R _ _ j x.P.g (Out.powIsPowGrp x.P.A j) x.v x.basis
  refine ⟨⟨P', Nat.mul_pos hj x.g_pos, _, hr', th, fun s => hne s fun _ => x.th_ne s, v, hv⟩,
    ⟨Out.powIsPowGrp x.P.A j, idIso _, idIso_isGen hL⟩, rfl, fun p => hr' p.1 p.2, fun jj b h => ?_, hvp⟩
  refine Eq.trans ?_ (th.compat jj b)
  rw [hth jj fun i => LB.wchart_le x.P.L _ jj i, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (congrArg (fun f => f.hom (x.th.f (jj i))) (Scheme.Hom.appLE_map (Out.powPr x.P.A i).left
    (LB.wchart_le x.P.L (fun i => (Out.powPr x.P.A i).left) jj i) (homOfLE (inf_le_left (b := P'.L.U b))).op)).symm

end GlobalTheory.KeyPow
