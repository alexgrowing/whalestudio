import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

namespace GlobalTheory.PolPull

theorem lbIso_polOf_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), ∀ (DY : EffCartierData Y.X) (DY' : EffCartierData Y'.X) (m : ℕ), IsOpenImmersion v → Nonempty (SABMap Y'.t Y.t v) → DY.idealSheaf.comap v = DY'.idealSheaf → ((polOf Y m DY).pull v).IsLB → (polOf Y' m DY').IsLB → LBIso (polOf Y' m DY') ((polOf Y m DY).pull v) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' v DY DY' m hv ⟨n⟩ hI hP hP'
  have hA' := PolFin.isLB_detLie_of_polOf hP'
  have hdet : LBIso ((detLie Y).pull v) (detLie Y') := PolFin.lbIso_detLie n.cart
  have hk : DY.KeepsRegular v := (DY.keepsRegular_iff_effCartier v).2 (hI.symm ▸ DY'.effCartier_idealSheaf)
  have hB := pull_isLB DY.isLB_lb v
  have hdiv : LBIso DY'.lb (DY.lb.pull v) :=
    LBIso.trans DY'.isLB_lb (DY.pull v hk).isLB_lb hB
      (EffCartierData.lbIso_of_idealSheaf_eq _ _ (hI.symm.trans (DY.idealSheaf_pull v hk).symm))
      (DY.lbIso_pull v hk)
  have hAv : ((detLie Y).pull v).IsLB := by
    refine isLB_of_ev _ (eq_top_iff.2 fun y _ => ?_) fun I J K S _ z hij hjk hik => ?_
    · obtain ⟨J, hJ⟩ := TopologicalSpace.Opens.mem_iSup.1 (hP.cover.ge (Set.mem_univ y))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => (J PUnit.unit).1 PUnit.unit,
        mem_pull.2 (LB.wchart_le _ _ _ PUnit.unit (mem_pull.1 hJ).1)⟩
    · have le : ∀ I J : ((detLie Y).pull v).ι, ((detLie Y).pull v).U I ⊓ ((detLie Y).pull v).U J ≤
          v ⁻¹ᵁ ((detLie Y).U (I PUnit.unit) ⊓ (detLie Y).U (J PUnit.unit)) := fun I J =>
        le_inf (inf_le_left.trans (LB.wchart_le _ _ I PUnit.unit)) (inf_le_right.trans (LB.wchart_le _ _ J PUnit.unit))
      rw [PolFin.ev_pull_g _ v z I J hij (le_preimage_map v (le I J) hij),
        PolFin.ev_pull_g _ v z J K hjk (le_preimage_map v (le J K) hjk),
        PolFin.ev_pull_g _ v z I K hik (le_preimage_map v (le I K) hik)]
      exact ev_detChg_mul _ _ _ (z ≫ v) _ _ _
  have hQ : (CechPic.tens (lbPow (CechPic.dual ((detLie Y).pull v)) m) (CechPic.dual (DY.lb.pull v))).IsLB :=
    CechPic.isLB_tens (isLB_lbPow (CechPic.isLB_dual hAv) m) (CechPic.isLB_dual hB)
  have le : ∀ J : ((polOf Y m DY).pull v).ι, ((polOf Y m DY).pull v).U J ≤ (𝟙 Y'.X) ⁻¹ᵁ
      (CechPic.tens (lbPow (CechPic.dual ((detLie Y).pull v)) m) (CechPic.dual (DY.lb.pull v))).U
        (fun _ _ => (J PUnit.unit).1 PUnit.unit, fun _ => (J PUnit.unit).2) := fun J y hy =>
    ⟨mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy).1)), mem_pull.2 (mem_pull.1 hy).2⟩
  have ch : ChartPull ((polOf Y m DY).pull v)
      (CechPic.tens (lbPow (CechPic.dual ((detLie Y).pull v)) m) (CechPic.dual (DY.lb.pull v))) (𝟙 _) :=
    { idx := fun J => (fun _ _ => (J PUnit.unit).1 PUnit.unit, fun _ => (J PUnit.unit).2)
      le := le
      g := fun y J J' hJ hJ' => by
        have h1 := mem_pull.1 hJ
        have h2 := mem_pull.1 hJ'
        have k1 := le J hJ
        have k2 := le J' hJ'
        refine (gm_pull_g (polOf Y m DY) v (𝟙 _) y J J' hJ hJ').trans ?_
        refine (CechPic.gm_tens (lbPow (GlobalTheory.FlagMod.detOm Y) m) (CechPic.dual DY.lb) (𝟙 _ ≫ v) y _ _ h1 h2).trans ?_
        refine Eq.trans ?_ (CechPic.gm_tens _ _ (𝟙 _) y _ _ k1 k2).symm
        refine congrArg₂ (· * ·) ?_ ?_
        · refine (gm_lbPow_g m (𝟙 _ ≫ v) y _ _ h1.1 h2.1).trans ?_
          refine Eq.trans ?_ (gm_lbPow_g m (𝟙 _) y _ _ k1.1 k2.1).symm
          refine congrArg (· ^ m) ((map_inv _ _).trans (Eq.trans ?_ (map_inv _ _).symm))
          refine congrArg (·⁻¹) (Eq.symm ((gm_pull_g (detLie Y) v (𝟙 _) y _ _ (mem_powChart.1 k1.1) (mem_powChart.1 k2.1)).trans ?_))
          rfl
        · refine (map_inv _ _).trans (Eq.trans ?_ (map_inv _ _).symm)
          exact congrArg (·⁻¹) (gm_pull_g DY.lb v (𝟙 _) y _ _ k1.2 k2.2).symm }
  have hPQ : LBIso ((polOf Y m DY).pull v)
      (CechPic.tens (lbPow (CechPic.dual ((detLie Y).pull v)) m) (CechPic.dual (DY.lb.pull v))) :=
    CechPic.iso_of_chart hQ ch
  have cl : ∀ {X : Scheme.{0}} {L B : LB X} (hL : L.IsLB) (hB : B.IsLB)
      (h : (CechPic.tens (lbPow (CechPic.dual L) m) (CechPic.dual B)).IsLB),
      CechPic.cls _ h = m • -CechPic.cls L hL + -CechPic.cls B hB := fun hL hB h => by
    rw [CechPic.cls_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hB),
      CechPic.cls_lbPow (CechPic.isLB_dual hL), CechPic.cls_dual hL, CechPic.cls_dual hB]
  refine (CechPic.cls_eq_iff hP' hP).1 ((cl hA' DY'.isLB_lb hP').trans (Eq.trans ?_
    ((cl hAv hB hQ).symm.trans ((CechPic.cls_eq_iff hP hQ).2 hPQ).symm)))
  rw [(CechPic.cls_eq_iff hAv hA').2 hdet, (CechPic.cls_eq_iff DY'.isLB_lb hB).2 hdiv]

end GlobalTheory.PolPull
