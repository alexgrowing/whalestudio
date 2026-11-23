import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsChartUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoOfAssociatedGermsFlatStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PolAgree

open FieldDescentGen

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem crd_pull {X Y : Scheme.{0}} (φ : X ⟶ Y) (H : LB Y) {J : Type} (s : J → H.Sec) {R : Type} [CommRing R]
    (y : Sp R ⟶ X) (v : J → R) (h : Crd H s (y ≫ φ) v) :
    Crd (H.pull φ) (fun j => secPull H φ (s j)) y v := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hl' : ⊤ ≤ y ⁻¹ᵁ (H.pull φ).U (fun _ => l) := fun z hz => mem_pull.2 (hl hz)
  refine ⟨fun _ => l, c, hl', fun j => ?_⟩
  rw [hv j]
  congr 1
  unfold valR
  rw [dif_pos hl, dif_pos hl']
  congr 1
  change _ = (y.appLE _ ⊤ hl').hom ((φ.appLE _ _ (pull_le H φ (fun _ => l))).hom ((s j).f l))
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem mulA_comp {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (m : ℕ) :
    Out.mulA A m ≫ φ = φ ≫ Out.mulA B m := by
  unfold Out.mulA
  rw [MonObj.comp_pow, Category.comp_id]
  have := map_pow (IsMonHom.monoidHom φ A) (𝟙 A) m
  simpa using this

theorem lbIso_pull : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (s' : J → (lbPow P'.L N).Sec) (a : J) (θ : (lbPow P.L 1).Sec) (θ' : (lbPow P'.L 1).Sec) (φ : P.A ⟶ P'.A), 1 ≤ m → IsMonHom φ → ⨆ j, Out.nonzeroLocus (s j) = ⊤ → (∀ (F : Type) [Field F] (y : Sp F ⟶ P.A.left) (v : J → F), Crd (lbPow P.L N) s y v → Crd (lbPow P'.L N) s' (y ≫ φ.left) v) → (∃ l, θ.f l ≠ 0) → (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s a).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((θ).f l))) → (∀ (y : P'.A.left) k l, y ∈ (lbPow P'.L N).U k → (Out.mulA P'.A m).left y ∈ (lbPow P'.L 1).U l → Associated (gs (𝟙 P'.A.left) y ((lbPow P'.L N).U k) ((s' a).f k)) (gs (Out.mulA P'.A m).left y ((lbPow P'.L 1).U l) ((θ').f l))) → LBIso (P'.L.pull φ.left) P.L := by
  intro h K _ _ P P' N m J s s' a θ θ' φ hm hφ hs hcrd hθ hP hP'
  have := polAV_isIntegral_of_isAlgClosed K P
  have hL := P.isLB
  have hL' := P'.isLB
  have hN : (lbPow P.L N).IsLB := LB.isLB_linComb hL _ _
  have hN' : (lbPow P'.L N).IsLB := LB.isLB_linComb hL' _ _
  have h1 : (lbPow P.L 1).IsLB := LB.isLB_linComb hL _ _
  have h1' : (lbPow P'.L 1).IsLB := LB.isLB_linComb hL' _ _
  have hmul := h.mulN _ P m hm
  have hfl : Flat (Out.mulA P.A m).left := hmul.2.1
  have hsu : Surjective (Out.mulA P.A m).left := hmul.2.2.1
  have hc : (Out.mulA P.A m).left ≫ φ.left = φ.left ≫ (Out.mulA P'.A m).left := by
    rw [← Over.comp_left, mulA_comp, Over.comp_left]
  have hw := CrdIso.exists_chart_unit (H := lbPow P.L N) (H' := (lbPow P'.L N).pull φ.left) (s := s)
    (s' := fun j => secPull _ φ.left (s' j)) hs (fun F _ y v hv => crd_pull _ _ _ _ _ (hcrd F y v hv))
  have key : LBIso (lbPow P.L 1) ((lbPow P'.L 1).pull φ.left) := by
    refine GlobalTheory.T.lbIso_of_associated_germs_flat _ _ (Out.mulA P.A m).left _ _ θ (secPull _ φ.left θ') h1 (pull_isLB h1' _) hθ fun y => ?_
    obtain ⟨k, hk⟩ := exists_chart hN y
    obtain ⟨k', hk'⟩ := exists_chart hN' (φ.left y)
    obtain ⟨l, hl⟩ := exists_chart h1 ((Out.mulA P.A m).left y)
    obtain ⟨l', hl'⟩ := exists_chart h1' (φ.left ((Out.mulA P.A m).left y))
    have hl'' : (Out.mulA P'.A m).left (φ.left y) ∈ (lbPow P'.L 1).U l' := by
      rw [← Scheme.Hom.comp_apply, ← hc]; exact hl'
    have hlp : (Out.mulA P.A m).left y ∈ ((lbPow P'.L 1).pull φ.left).U (fun _ => l') := mem_pull.2 hl'
    have hkp : y ∈ ((lbPow P'.L N).pull φ.left).U (fun _ => k') := mem_pull.2 hk'
    refine ⟨l, fun _ => l', hl, hlp, ?_⟩
    have e1 : gs (Out.mulA P.A m).left y _ ((secPull _ φ.left θ').f (fun _ => l')) =
        (φ.left.stalkMap y).hom (gs (Out.mulA P'.A m).left (φ.left y) _ (θ'.f l')) := by
      rw [← gs_comp _ _ _ _ hl'', ← hc]
      exact gs_appLE _ _ _ _ _ _ hlp _
    have e2 : gs (𝟙 P.A.left) y _ ((secPull _ φ.left (s' a)).f (fun _ => k')) =
        (φ.left.stalkMap y).hom (gs (𝟙 P'.A.left) (φ.left y) _ ((s' a).f k')) := by
      rw [← gs_stalkMap _ _ _ hk']
      exact (gs_appLE _ _ _ _ _ _ hkp _).trans (by rw [Category.id_comp])
    obtain ⟨w, hw⟩ := hw k (fun _ => k')
    have hx : (𝟙 P.A.left : _ ⟶ _) y ∈ ((lbPow P'.L N).pull φ.left).U (fun _ => k') ⊓ (lbPow P.L N).U k :=
      ⟨hkp, hk⟩
    have e := congrArg (gs (𝟙 P.A.left) y _) (hw a)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, gs_unit _ _ _ hx, e2] at e
    have a1 := (hP' (φ.left y) k' l' hk' hl'').map (φ.left.stalkMap y).hom
    rw [e1]
    refine (hP y k l hk hl).symm.trans (Associated.trans ?_ a1)
    exact ⟨_, (_root_.mul_comm _ _).trans e.symm⟩
  have e := (CechPic.cls_eq_iff h1 (pull_isLB h1' _)).2 key
  rw [CechPic.cls_lbPow hL, CechPic.cls_pull h1', CechPic.cls_lbPow hL', one_smul, one_smul] at e
  rw [← CechPic.cls_eq_iff (pull_isLB hL' _) hL, CechPic.cls_pull hL', e]

end GlobalTheory.ZH.PolAgree
end
