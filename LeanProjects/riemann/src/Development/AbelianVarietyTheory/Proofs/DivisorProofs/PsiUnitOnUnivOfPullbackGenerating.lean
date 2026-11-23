import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QkIsPullFLeftIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullGenAll

theorem pullgen : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R'), IsPullDeg φ D D' → (∀ χ, PsiUnitOn D χ Set.univ) → ∀ x, PsiUnitOn D' x Set.univ := by
  intro R R' _ _ _ _ φ D D' hD h x
  choose t ht H using fun χ => (GlobalTheory.ArcPull.psiUnitOn_univ_iff D χ).1 (h χ)
  have hpsi : ∀ χ, hD.psiW.psi χ = LB.pullGen D.P.L _ _ (t χ) hD.W.ι := by
    intro χ
    rw [GlobalTheory.GtRestrictCompare.psiOn_unique hD.psiW
      ⟨fun χ => LB.pullGen D.P.L _ _ (t χ) hD.W.ι,
        fun χ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (ht χ) _,
        fun χ => corr_of_val D.P.isLB fun y J hJ => by
          refine (val_pull hJ _ _ _).trans ((val_pull hJ (t χ) _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
          rw [← val_corr hJ (H χ), val_pull hJ, Category.assoc, Category.assoc, morphismRestrict_ι]⟩]
  obtain ⟨a, ha, va⟩ := GlobalTheory.ArcPull.exists_down_om hD.w_gen D.P.isLB D'.P.isLB (Y' := Sp R') (K := PUnit)
    (φ' := fun _ => (D'.c x).left) (spMap φ) (fun _ => hD.c_pr x) (t (hD.xe x)) (ht _)
  refine (GlobalTheory.ArcPull.psiUnitOn_univ_iff D' x).2 ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have c : val (hD.psiW.psi (hD.xe x)) (𝟙 _ ≫ hD.g) y J = val (t (hD.xe x)) ((𝟙 _ ≫ jK R') ≫ spMap φ) y J := by
    rw [hpsi]
    refine (val_pull hJ (t (hD.xe x)) _ _).trans ?_
    have q : (𝟙 _ ≫ hD.g) ≫ hD.W.ι = (𝟙 _ ≫ jK R') ≫ spMap φ := by
      rw [Category.assoc, hD.g_comm, Category.assoc]
      rfl
    exact congrArg (fun q => val (t (hD.xe x)) q y J) q
  have e := ((GlobalTheory.PsiEvenPull.psi_pull hD x (𝟙 _) y hJ hJ').symm.trans c).trans
    (va _ (𝟙 _ ≫ jK R') y J J' hJ hJ')
  rw [Fintype.prod_unique, zpow_neg_one, Category.assoc] at e
  exact (val_pull hJ' _ _ _).trans (mul_left_cancel e).symm

end GlobalTheory.PullGenAll
