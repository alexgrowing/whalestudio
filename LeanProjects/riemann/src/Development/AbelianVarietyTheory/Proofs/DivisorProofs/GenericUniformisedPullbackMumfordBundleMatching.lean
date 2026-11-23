import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem genLam_pull_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → Geo.Tor.IsSquare βW βW₂ → LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) → ∃ (ga : FractionRing R →+* FractionRing W) (α : AW.A.left ⟶ A.A.left) (α₂ : (G2 AW.A).left ⟶ (G2 A.A).left), (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧ IsGrpPullback AW.A A.A (spMap ga) α ∧ Geo.Tor.IsSquare α α₂ ∧ LBIso (abelian₂ AW.A AW.L) ((abelian₂ A.A A.L).pull α₂) ∧ UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hExt W _ _ _ φ GW _ _ βW βW₂ DW AW UW hW hφ hφl hβ hsqW hPP
  let ga : FractionRing R →+* FractionRing W := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ
  have hga : ∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r) := fun r => by
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  let κW : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst _ _ ≫ βW) (pullback.snd _ _ ≫ spMap ga) (by
      rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κW ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := pullback.lift_fst _ _ _
  have w : κW ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GW).hom ≫ spMap ga :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GW) ((Over.pullback (jK R)).obj G) (spMap ga) κW :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GW (jK W)).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK W)).obj GW) := Functor.isCommMonObj_obj
  have : IsMonHom UW.gen.hom := UW.gen_hom
  have : IsMonHom gen.hom := hgen
  have : IsMonHom UW.gen.symm.hom := show IsMonHom UW.gen.inv by infer_instance
  have hu : IsGrpPullback AW.A ((Over.pullback (jK W)).obj GW) (𝟙 _) UW.gen.inv.left :=
    isGrpPullback_of_iso UW.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G) A.A (𝟙 _) gen.hom.left := isGrpPullback_of_iso gen
  have hα : IsGrpPullback AW.A A.A (spMap ga) (UW.gen.inv.left ≫ κW ≫ gen.hom.left) :=
    (hu.comp (hκ.comp hg)).congr (by simp) rfl
  obtain ⟨u₂, squ, Hu⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hu
  obtain ⟨κ₂, sqκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hκ
  obtain ⟨g₂, sqg, Hg⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hg
  obtain ⟨fW₂, sqfW, HfW⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback GW (jK W))
  obtain ⟨fR₂, sqfR, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback G (jK R))
  have hLA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLG : (UW.LG.L.pull (pullback.fst GW.hom (jK W))).IsLB := pull_isLB UW.LG.isLB _
  have hAg : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _

  have Z : LBIso (abelian₂ ((Over.pullback (jK R)).obj G) (A.L.pull gen.hom.left)) ((abelian₂ A.A A.L).pull g₂) := by
    have h := Hg A.L (A.L.pull gen.hom.left) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hAg hLA
      (PolBaseChange.lbIso_refl hAg)
      (LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl hLA))
    rwa [Category.comp_id] at h
  have Y : LBIso (PP.pull fR₂) ((abelian₂ A.A A.L).pull g₂) :=
    LBIso.trans (pull_isLB hExt.1 _) (DVR.linComb_isLB _ hAg _ _) (pull_isLB hLA _) (hExt.2 fR₂ sqfR).symm Z
  have e : fW₂ ≫ βW₂ = κ₂ ≫ fR₂ := by
    apply pullback.hom_ext
    · show (fW₂ ≫ βW₂) ≫ (fst G G).left = (κ₂ ≫ fR₂) ≫ (fst G G).left
      simp only [Category.assoc, hsqW.1, sqfR.1]
      rw [← Category.assoc fW₂, sqfW.1, reassoc_of% sqκ.1, hκf, Category.assoc]
    · show (fW₂ ≫ βW₂) ≫ (snd G G).left = (κ₂ ≫ fR₂) ≫ (snd G G).left
      simp only [Category.assoc, hsqW.2, sqfR.2]
      rw [← Category.assoc fW₂, sqfW.2, reassoc_of% sqκ.2, hκf, Category.assoc]
  have B1 : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      (PP.pull (κ₂ ≫ fR₂)) := by
    have h := HfW UW.LG.L (UW.LG.L.pull (pullback.fst GW.hom (jK W))) _ PP βW₂ UW.LG.isLB hLG hExt.1
      (PolBaseChange.lbIso_refl hLG) hPP
    rwa [e] at h
  have B3 : LBIso (PP.pull (κ₂ ≫ fR₂)) ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.chartPull (chartPullSame PP _ (fun _ => fR₂) _ κ₂ fun _ => rfl)
      (chartPullSame (abelian₂ A.A A.L) _ (fun _ => g₂) _ κ₂ fun _ => rfl) Y
  have hLamW : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.trans (DVR.linComb_isLB _ hLG _ _) (pull_isLB hExt.1 _) (pull_isLB hLA _) B1 B3

  have hN : LBIso AW.L ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) := by
    have hext : LBIso (AW.L.pull UW.gen.hom.left) (UW.LG.L.pull (pullback.fst GW.hom (jK W))) := UW.ext
    have h1 : LBIso (AW.L.pull (𝟙 _)) ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) :=
      LBIso.chartPull (chartPullSame AW.L _ (fun _ => UW.gen.hom.left) _ UW.gen.inv.left fun _ => by
          rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left])
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) hext
    have h0 : LBIso AW.L (AW.L.pull (𝟙 _)) :=
      LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl AW.isLB)
    exact LBIso.trans AW.isLB (pull_isLB AW.isLB _) (pull_isLB hLG _) h0 h1
  refine ⟨ga, UW.gen.inv.left ≫ κW ≫ gen.hom.left, u₂ ≫ κ₂ ≫ g₂, hga, hα, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Category.assoc, sqg.1, reassoc_of% sqκ.1, reassoc_of% squ.1]
  · simp only [Category.assoc, sqg.2, reassoc_of% sqκ.2, reassoc_of% squ.2]
  · exact Hu _ AW.L _ (abelian₂ A.A A.L) (κ₂ ≫ g₂) hLG AW.isLB hLA hN hLamW
  · rw [Category.assoc, Category.assoc, ← Category.assoc gen.hom.left, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.id_comp, hκf]

end GlobalTheory.Mum
