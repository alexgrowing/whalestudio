import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
noncomputable section

namespace GlobalTheory.HomFixMat

theorem appLE_res_pull {X Y Z : Scheme.{0}} (φ : Y ⟶ Z) (h : X ⟶ Y) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ φ ⁻¹ᵁ U) (e₂ : W ≤ h ⁻¹ᵁ V) (e₃ : W ≤ (h ≫ φ) ⁻¹ᵁ U) (u : Γ(Z, U)) :
    (h.appLE V W e₂).hom ((Y.presheaf.map (homOfLE e₁).op).hom ((φ.app U).hom u)) =
      (X.presheaf.map (homOfLE e₃).op).hom (((h ≫ φ).app U).hom u) := by
  simp only [← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_comp_appLE]

theorem appLE_restrict {X Y : Scheme.{0}} (h : X ⟶ Y) (V V' : Y.Opens) (W W' : X.Opens) (eV : V' ≤ V)
    (eW : W' ≤ W) (e : W ≤ h ⁻¹ᵁ V) (e' : W' ≤ h ⁻¹ᵁ V') (x : Γ(Y, V)) :
    (X.presheaf.map (homOfLE eW).op).hom ((h.appLE V W e).hom x) =
      (h.appLE V' W' e').hom ((Y.presheaf.map (homOfLE eV).op).hom x) := by
  simp only [← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem pullSec_exists : ∀ {X Y Z : Scheme.{0}} (L : LB Z) (φ : Y ⟶ Z) (h : X ⟶ Y) (a : ℤ)
    (s : LB.Sec (powPull L φ a)), ∃ s' : LB.Sec (powPull L (h ≫ φ) a), ∀ q : Fin 1 → L.ι,
      s'.f q = (h.appLE (LB.wchart L (fun _ : Fin 1 => φ) q) (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q)
        (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q) := by
  intro X Y Z L φ h a s
  refine ⟨⟨fun q => (h.appLE _ _ (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q), ?_⟩, fun q => rfl⟩
  intro (q : Fin 1 → L.ι) (q' : Fin 1 → L.ι)
  have e0 : LB.wchart L (fun _ : Fin 1 => h ≫ φ) q ⊓ LB.wchart L (fun _ : Fin 1 => h ≫ φ) q' ≤
      h ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => φ) q ⊓ LB.wchart L (fun _ : Fin 1 => φ) q') :=
    fun x hx => ⟨GlobalTheory.HomFixMat.wchart_comp_le L h φ q hx.1, GlobalTheory.HomFixMat.wchart_comp_le L h φ q' hx.2⟩
  refine (appLE_restrict h _ _ _ _ inf_le_left inf_le_left _ e0 _).trans ?_
  refine (congrArg _ (s.compat q q')).trans ?_
  refine (map_mul _ _ _).trans ?_
  congr 1
  · have hg : ((powPull L (h ≫ φ) a).g q q') =
        Units.map (h.appLE _ _ e0).hom.toMonoidHom ((powPull L φ a).g q q') := by
      show (∏ k : Fin 1, _) = Units.map _ (∏ k : Fin 1, _)
      rw [map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_zpow]
      congr 1
      ext
      exact (appLE_res_pull φ h (L.U (q 0) ⊓ L.U (q' 0))
        (LB.wchart L (fun _ : Fin 1 => φ) q ⊓ LB.wchart L (fun _ : Fin 1 => φ) q')
        (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q ⊓ LB.wchart L (fun _ : Fin 1 => h ≫ φ) q') _ e0 _
        (L.g (q 0) (q' 0) : Γ(Z, L.U (q 0) ⊓ L.U (q' 0)))).symm
    rw [hg]
    rfl
  · exact (appLE_restrict h _ _ _ _ inf_le_right inf_le_right _ e0 _).symm

end GlobalTheory.HomFixMat
