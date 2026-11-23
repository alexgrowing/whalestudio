import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.TorusCoordPull in

theorem isPullPt_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  intro R R' _ _ _ _ ρ D I E hE A' G' _ _ U Y e φ h Z g
  obtain ⟨ξ', hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt e)
    (T := Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)) g rfl
  have hp := Y.rep.1 (Over.mk ((g ≫ φ) ≫ Y.H.hom)) Y.H (Over.homMk (g ≫ φ) rfl) (𝟙 Y.H)
  rw [Category.comp_id] at hp
  set Yξ := Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl) with hYξ
  have hb : ξ'.b.left ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) = 𝟙 Z ≫ Yξ.b.left := by
    rw [hξ.1, Category.assoc, h.1, hp.1, Category.id_comp]
    rfl
  refine ⟨ξ', hξ, hb, fun χ => ?_⟩
  have hψ : ∀ κ : Fin 4, DegPre.gtφT E.toPre _ ξ'.b χ κ ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) =
      𝟙 Z ≫ DegPre.gtφT D _ Yξ.b (hE.xe χ) κ := fun κ => by
    rw [GlobalTheory.TorusCoord.gtφT_eq, GlobalTheory.TorusCoord.gtφT_eq]
    exact Oφ_pull hE Yξ.b ξ'.b (𝟙 Z) hb χ κ
  refine ⟨hψ, maps_of_good ((isGen_iff hE.w).1 hE.w_gen) D.P.isLB E.toPre.P.isLB (ξ'.s χ) (ξ'.isGen χ) _
    (Yξ.isGen _) hψ fun z J J' hJ hJ' => ?_⟩
  have o := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (U.gt e).pG (𝟙 Z) g (by rw [Category.id_comp]; exact hξ.1)).1 χ
  have r1 : val (Yξ.s (hE.xe χ)) (𝟙 Z) z J = val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) (g ≫ φ) z J :=
    (val_corr hJ (hp.2 _) (𝟙 _)).trans ((val_pull hJ _ _ _).trans
      (congrArg (fun r => val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) r z J) (Category.id_comp _)))
  have r3 : val (ξ'.s χ) (𝟙 Z) z J' = val ((U.gt e).t χ) g z J' :=
    (val_corr hJ' (hξ.2 χ) (𝟙 _)).trans ((val_pull hJ' _ _ _).trans
      (congrArg (fun r => val ((U.gt e).t χ) r z J') (Category.id_comp _)))
  refine r1.trans ((h.2 χ Z g z J J' hJ hJ').trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) r3.symm))
  have ok := o k
  rw [Category.id_comp] at ok
  rw [← ok]
  rfl

end GlobalTheory.Mum
