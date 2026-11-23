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

noncomputable section

namespace GlobalTheory.PreLiftData

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PreLift

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_rescale_isPullDeg_data {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left) :
    ∃ (κ : D'.X → (FractionRing R')ˣ) (hD : IsPullDeg i D (GlobalTheory.PolDeg.rescale D' κ)),
      (∀ y, hD.xe y = xe y) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = Φ ∧ hD.W = W := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  choose u hu using GlobalTheory.FieldPull.exists_psi_ratio D' psi hpsi
  refine ⟨fun x => (u x)⁻¹, ?_⟩
  have eψ : ∀ x, psi x = (GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi x := fun x =>
    GlobalTheory.TorusExt.gen_ext_val D'.P.isLB (hpsi x) ((GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi_gen x)
      fun y J' hJ' => by
        refine Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ').symm
        have h1 : unitOn (u x)⁻¹ * unitOn (u x) = 1 := (map_mul _ _ _).symm.trans
          ((congrArg unitOn (inv_mul_cancel (u x))).trans (map_one _))
        rw [hu x y J' hJ', GlobalTheory.TauTwist.unitAt_apply, ← _root_.mul_assoc, ← map_mul]
        erw [h1]
        rw [map_one, _root_.one_mul]
  have key : ∀ x, GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit)
      (fun _ => e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) w (D'.xK x) (-1) (psi x) (b x) := fun x jN jL => by
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, eψ x ▸ key x,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, fun _ => rfl, rfl, rfl⟩
  exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
    (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr

theorem exists_rescale_isPullDeg_top : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  intro _ _ _ _ _ _ θ₀ D₀ Q e β hU gp hL hc
  obtain ⟨ψW⟩ := GlobalTheory.ArcPull.nonempty_psiOn_top D₀ hU
  let gg : (TK _).left ⟶ (TW (⊤ : (Sp _).Opens)).left := (jK _ ≫ specOf θ₀) ≫ (Sp _).topIso.inv
  have hg : gg ≫ (⊤ : (Sp _).Opens).ι = jK _ ≫ specOf θ₀ := by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨w₀, hw₀⟩ := hL
  have he : eSec Q.P.A ≫ β = spMap θ₀ ≫ eSec D₀.P.A := (cubeMapOf gp).e_comm
  have hσ : eSec Q.P.A ≫ Q.P.A.hom = 𝟙 _ := Over.w η[Q.P.A]
  obtain ⟨w, hw, hr⟩ := GlobalTheory.UnifPreCompare.exists_rigidified D₀.P.isLB Q.P.isLB Q.P.A.hom (eSec Q.P.A) hσ w₀ hw₀
    Q.rig Q.rig_gen (φ := eSec D₀.P.A) D₀.rig D₀.rig_gen (spMap θ₀) he
  exact exists_rescale_isPullDeg_data (i := θ₀) D₀ Q ψW gg hg gp w ((isGen_iff w).1 hw) hr e hc

end GlobalTheory.PreLiftData
