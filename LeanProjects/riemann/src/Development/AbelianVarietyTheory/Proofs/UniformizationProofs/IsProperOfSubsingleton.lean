import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfExpBij
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyLinearEquivOfRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationUnconditionaStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRankOneNonproperPowerSeriesStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TateUnif

theorem isProper_of_subsingleton {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) [Subsingleton D.X] :
    IsProper (thickObj R I e G).hom := by
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hp := g.isKernel
  have : Mono g.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := GlobalTheory.UU.point_eq_of_subsingleton _ _
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono g.q.left := inferInstanceAs (Mono ((Over.forget _).map g.q))
  have : EffectiveEpi g.q.left := inferInstance
  have : IsIso g.q.left := isIso_of_mono_of_strongEpi _
  have := D.P.isAb.proper
  have : IsProper (thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  rw [← Over.w g.q]
  infer_instance

theorem rank_add_dim {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    Module.finrank ℤ D.toPre.X + D.toPre.P.g = A.g := by
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  have := hG.geomConnected
  have h₁ := GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hR D A G U.toUnifPre 2 one_le_two
    (U.expand 2 one_le_two)
  have h₂ := (GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2
    one_le_two).2
  exact Nat.pow_right_injective le_rfl (h₂.symm.trans h₁)

theorem exists_unif_rank_one : ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries ℚ))))) (G : Over (Spec (CommRingCat.of (PowerSeries ℚ)))) (_ : GrpObj G) (_ : IsCommMonObj G) (D : DegData (PowerSeries ℚ) (IsLocalRing.maximalIdeal (PowerSeries ℚ))) (_ : Unif (IsLocalRing.maximalIdeal (PowerSeries ℚ)) D A G), IsSemiAbelian G ∧ A.g = 1 ∧ Module.finrank ℤ D.toPre.X = 1 ∧ D.toPre.P.g = 0 := by
  obtain ⟨A, G, _, _, s, hA, -, hnp⟩ := GlobalTheory.T.exists_rank_one_nonproper_power_series
  obtain ⟨D, U, -⟩ := GlobalTheory.T.exists_degenerationData_uniformisation_unconditional (PowerSeries ℚ) A G s
  have hR : AdmBase (PowerSeries ℚ) (IsLocalRing.maximalIdeal (PowerSeries ℚ)) :=
    ⟨inferInstance, inferInstance, inferInstance, s.cdvr.2.1⟩
  have h := rank_add_dim hR s.semi U
  have h0 : Module.finrank ℤ D.toPre.X ≠ 0 := fun h0 => by
    have : Subsingleton D.toPre.X := Module.finrank_zero_iff.1 h0
    exact hnp (isProper_of_subsingleton (U.gt 0))
  exact ⟨A, G, inferInstance, inferInstance, D, U, s.semi, hA, by omega, by omega⟩

end GlobalTheory.TateUnif
