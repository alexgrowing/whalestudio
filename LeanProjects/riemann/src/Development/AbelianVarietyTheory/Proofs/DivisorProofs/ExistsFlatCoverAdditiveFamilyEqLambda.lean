import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedKernelClosedFiniteFlatAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreementLocusOfAffineOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCover

theorem exists_cover : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left) (hN : Fam A N), ∃ (H : Over (Sp R)) (h : H ⟶ T) (x : H ⟶ A), Flat h.left ∧ Surjective h.left ∧ QuasiCompact h.left ∧ (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H), evc hN.isLB a (y ≫ h) = GlobalTheory.CechPic.pull (a * (y ≫ x)).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull (y ≫ x).left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  intro R _ _ A _ g hA _ L hL hamp T N hN
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have eP : ∀ (Y : Over (Sp R)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have loc : ∀ V : T.left.affineOpens, ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ Over.mk (V.1.ι ≫ T.hom)),
      IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A (Over.mk (V.1.ι ≫ T.hom))).left ∧
      Flat (h ≫ snd A (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd A (Over.mk (V.1.ι ≫ T.hom))).left ∧
      ∀ (Y : Over (Sp R)) (u : Y ⟶ A) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)),
        Same A (abelian₂ A L) N u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
    intro V
    haveI : IsAffine (Over.mk (V.1.ι ≫ T.hom)).left := V.2
    set j : Over.mk (V.1.ι ≫ T.hom) ⟶ T := Over.homMk V.1.ι rfl
    have hNV : (ev N (fst A (Over.mk (V.1.ι ≫ T.hom))) (snd A _ ≫ j)).IsLB := pull_isLB hN.isLB _
    have eV : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)),
        evc hNV a t = evc hN.isLB a (t ≫ j) := fun Y a t ↦ by
      rw [evc_ev hN.isLB, lift_fst, lift_snd_assoc]
    have fV : Fam A (ev N (fst A (Over.mk (V.1.ι ≫ T.hom))) (snd A _ ≫ j)) :=
      ⟨hNV, (isAdditive_iff hNV).2 fun Y a a' t ↦ by
        rw [eV, eV, eV]; exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (t ≫ j)⟩
    obtain ⟨H, h, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_twistedKernel_closed_finiteFlat_affineBase R A hA L hL hamp _ _ fV
    refine ⟨H, h, h1, h2, h3, h4, fun Y u t ↦ ?_⟩
    rw [← h5, same_iff hP hN.isLB, same_iff hP hNV, eV, Category.assoc]
  obtain ⟨H, h, -, hfin, hfl, hsu, hrep⟩ := GlobalTheory.T.exists_lineBundleFamily_agreementLocus_of_affineOpens R A hA A T (abelian₂ A L) N hP hN.isLB
    (fun Y u ↦ by rw [eP, lam_one_left]) (fun Y t ↦ hN.add.evc_one hN.isLB t) loc
  refine ⟨H, h ≫ snd A T, h ≫ fst A T, hfl, hsu, inferInstance, fun Y a y ↦ ?_⟩
  have hs : Same A (abelian₂ A L) N (y ≫ h ≫ fst A T) (y ≫ h ≫ snd A T) :=
    (hrep Y _ _).2 ⟨y, by ext <;> simp⟩
  have e := congrArg (CechPic.pull (lift a (𝟙 Y)).left) ((same_iff hP hN.isLB _ _).1 hs)
  rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp, lift_snd_assoc, Category.id_comp, eP] at e
  rw [← e, lam]

end GlobalTheory.DualCover
