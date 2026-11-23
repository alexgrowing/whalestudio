import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullTopUnit
open GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

theorem psiUnitOn_pull_top {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (hW : hD.W = ⊤) (x : D'.X) :
    PsiUnitOn D' x Set.univ := by
  have hI : IsIso hD.W.ι := by rw [hW, ← Scheme.topIso_hom]; infer_instance
  let h : Sp R' ⟶ (TW hD.W).left := specOf φ ≫ inv hD.W.ι
  have hh : h ≫ hD.W.ι = specOf φ := by simp [h]
  have hg : hD.g = jK R' ≫ h := by
    rw [← cancel_mono hD.W.ι, hD.g_comm, Category.assoc, hh]
  have sq : (D'.c x).left ≫ proj hD = h ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
    rw [hD.c_pr x, ← hh, Category.assoc]; rfl
  obtain ⟨a, ha, va⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (Y' := Sp R') (K := PUnit)
    (φ' := fun _ => (D'.c x).left) h (fun _ => sq) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
  refine (psiUnitOn_univ_iff D' x).2 ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have e₁ := PsiEvenPull.psi_pull hD x (𝟙 _) y hJ hJ'
  have e₂ := va _ (𝟙 _ ≫ jK R') y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_neg_one, Category.assoc (𝟙 _) (jK R') h, ← hg] at e₂
  have e := e₁.symm.trans e₂
  exact (val_pull hJ' _ _ _).trans (mul_left_cancel e).symm

end GlobalTheory.PullTopUnit
