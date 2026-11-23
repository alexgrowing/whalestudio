import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_gen_mulPull_pow_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (n k k' : ℕ), k' = k * n ^ 2 → ∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, (𝟙 G ^ n).left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen := by
  intro R _ _ I D A G _ _ U n k k' hk
  have hL := U.LG.isLB
  have hcube : GlobalTheory.MulPull.HasGen U.LG.L (thφ G (x3 G)) thε := ⟨U.cubG.t, U.cubG.isGen⟩
  have hrig : GlobalTheory.MulPull.HasGen U.LG.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) :=
    ⟨U.LG.rig, U.LG.rigGen⟩
  have hneg : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] :=
    ⟨U.symG, U.symG_gen⟩
  have main : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(𝟙 G : G ⟶ G).left, (𝟙 G ^ n).left]
      ![(n : ℤ) ^ 2, -1] := by
    refine GlobalTheory.MulPull.hasGen_pow hL hcube (𝟙 G) ?_ ?_ n
    · refine (hrig.pull (toUnit G).left).of_formEq hL (fun W _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine hneg.inv.of_formEq hL (fun W _ h => ?_)
      have e : ((𝟙 G : G ⟶ G)⁻¹) = ι[G] := Category.id_comp _
      rw [e]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        _root_.mul_one, neg_neg]
      exact _root_.mul_comm _ _
  obtain ⟨t, ht⟩ := main
  have hp : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(𝟙 G : G ⟶ G).left, (𝟙 G ^ n).left]
      (fun i => (k : ℤ) * (![(n : ℤ) ^ 2, -1] : Fin 2 → ℤ) i) := ⟨_, powGen_isGen _ _ _ t ht k⟩
  refine hp.of_formEq hL (fun W _ h => ?_)
  subst hk
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    _root_.mul_one, mul_neg]
  push_cast
  rfl

end GlobalTheory.UT
