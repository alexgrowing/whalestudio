import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleRigidifiedSquareIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationSquaresAgreeAtEachThickeningStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquareStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnifSqCompare

theorem mem_sq {X : Scheme.{0}} {L : LB X} {x : X} {j : L.ι} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ↔ x ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun _ => h⟩

end UnifSqCompare

set_option maxHeartbeats 1000000 in
open UnifCompare UnifSqCompare in

theorem unif_sq_polarised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' hL
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hGF : GlobalFnsSt := allSixLaws.1.globalFns
  have hS : SecBaseChangeSt := allSixLaws.1.secBaseChange
  have hA : AmpleSt := allSixLaws.1.ample
  obtain ⟨wL₀, hwL₀⟩ := hL
  obtain ⟨wL, hwL, hrig⟩ := GlobalTheory.T.exists_rescale_rigidified_square_iso _ G U.LG U'.LG wL₀ hwL₀
  choose β hβm hβ using unifPre_abelianPart_iso R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre
  choose v hvg hv using fun e =>
    GlobalTheory.T.polarization_squares_agree_at_each_thickening hGF R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre wL hwL hrig e (β e) (hβm e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R (maximalIdeal R) e D.toPre.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q U'.toUnifPre, Category.assoc, hβl,
      trans_comp_q U.toUnifPre, ← Category.assoc, hβl]
  have hR' := hR
  obtain ⟨hN, -, -, hC⟩ := hR'
  obtain ⟨Φ, w, hw, H⟩ := GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square hS hA R (maximalIdeal R) D.toPre.P D'.toPre.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R (maximalIdeal R) e D'.toPre.P.A).left,
        y ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') →
        thickMap R (maximalIdeal R) e D'.toPre.P.A y ∈
          ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β (e + 1)).hom.left ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) (e + 1) D'.toPre.P.A).left).U (fun _ => fun _ => j') := by
      intro y hy
      have k : thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left ≫
          (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left =
          (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j)) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j')) (trans_comp_proj e _)).mpr (mem_pull.1 hy.2))⟩
    have hz : r z ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') :=
      ⟨mem_pull.2 (mem_sq.2 hj), mem_pull.2 (mem_sq.2 hj')⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hp e)).mp (mem_sq.1 (mem_pull.1 hx.1))
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_sq.1 (mem_pull.1 hx.2)
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R (maximalIdeal R) e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U'.toUnifPre e x j' jL' hM' hL', gw_trans U.toUnifPre e x j jL hM hL, trans_comp_q U'.toUnifPre,
      trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have hpG : ∀ e, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot (maximalIdeal R)
  have hΦ : IsMonHom Φ.hom := by
    refine AbelianPartIso.isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine AbelianPartIso.isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R (maximalIdeal R) e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (hpG e)))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨Φ, w, wL, hw, hwL, hΦ, fun e => ⟨hpG e, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
    ((congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hp e)).mpr hM) hM'
  rw [Category.assoc] at h
  exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

end GlobalTheory
