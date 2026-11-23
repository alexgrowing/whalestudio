import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfRed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorusLift

open GlobalTheory.UU GlobalTheory.FormalPoint

section Lift

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)

theorem exists_coords (g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) (e : ℕ) :
    ∃ y : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left,
      RedOnto.Coords U e g (thick R I e) y :=
  RedOnto.exists_coords U e g (thick R I e) (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)

variable [IsLocalRing R]

variable {U} in

theorem red_unique [IsHausdorff I R] {g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    {x x' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} (h : U.Red x g) (h' : U.Red x' g) : x = x' := by
  choose y hy using exists_coords U g
  refine Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e => ?_)
  exact (RedOnto.comp_fstG_eq h (hy e)).symm.trans (RedOnto.comp_fstG_eq h' (hy e))

theorem exists_red [IsAdicComplete I R] (g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G, U.Red x g := by
  choose y hy using exists_coords U g
  have hf : IsAdicFamily I fun e => y e ≫ (fstG I e G).left := fun e => by
    have h₁ := (hy (e + 1)).comp (adicLevelMap I (Nat.le_succ (e + 1)))
    have h₂ : adicLevelMap I (Nat.le_succ (e + 1)) ≫ thick R I (e + 1) = thick R I e := adicLevelMap_ι _ _
    have h₃ : RedOnto.Coords U (e + 1) g (thick R I e) (adicLevelMap I (Nat.le_succ (e + 1)) ≫ y (e + 1)) :=
      h₂ ▸ h₁
    have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) G).left)
      (h₃.unique (hy e).succ)).trans ((Category.assoc _ _ _).trans (congrArg _ h₄)))
  obtain ⟨x, ⟨hx₁, hx₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (I := I) (𝟙 _) G.hom hf fun e => by
    have h₁ : (fstG I e G).left ≫ G.hom = (U.gt e).pG.left ≫ D.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    exact (Category.assoc _ _ _).trans ((congrArg _ h₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.P.A.hom) (hy e).1).trans ((Category.assoc _ _ _).trans (congrArg _ (Over.w g.b))))))
  refine ⟨Over.homMk x hx₁, fun e Z r xe hxe => ?_⟩
  have hr : r = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    have := congrArg (· ≫ G.hom) hxe
    simp only [Category.assoc, Over.homMk_left, hx₁] at this
    rw [← Category.comp_id r]
    refine this.symm.trans ?_
    rw [Over.w (fstG I e G)]
    rfl
  have hxe' : xe = (xe ≫ (thickObj R I e G).hom) ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, ← hx₂ e, hxe]
    simp only [Over.homMk_left]
    rw [hr, Category.assoc]
  have := (hy e).comp (xe ≫ (thickObj R I e G).hom)
  rw [← hr, ← hxe'] at this
  exact this

end Lift

theorem exists_sec_sq_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) := by
  intro R _ _ _ hR D A G _ _ hS U g hg
  obtain ⟨z, hz, hgz⟩ := hg
  have : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  obtain ⟨w, hw⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre GlobalTheory.globalFns_holds hS w hw
  obtain ⟨a, ha⟩ := exists_red U' g
  refine ⟨a, ?_, fun e ae _ hae => ?_⟩
  · rw [pow_two]
    exact red_unique (RedAdd.red_mul GlobalTheory.globalFns_holds ha ha hgz) (RedAdd.red_one U' hz)
  · obtain ⟨h₁, h₂⟩ := ha e _ (thick R (maximalIdeal R) e) ae hae
    refine ⟨h₁, fun χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩
    rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
    exact h₂ χ y J hJ

end GlobalTheory.TorusLift
