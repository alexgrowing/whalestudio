import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.MumAmple

theorem relAmple_of_lam_iso_univ : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R' : Type) [CommRing R'] [IsNoetherianRing R'] (T : Sp R' ⟶ F.X) (B : Over (Sp R')) [GrpObj B] [IsCommMonObj B] (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A T β → IsSquare β β₂ → ∀ L : LB B.left, L.IsLB → LBIso (abelian₂ B L) (F.univ.P.pull β₂) → RelAmple B L := by
  intro o _ ζ g n F R' _ _ T B _ _ β β₂ hpb hsq L hL hiso
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hpb
  have := hB.proper
  have := hB.smooth
  refine ProperFinite.relAmple_of_geometricFibres B hL fun K _ _ y => ?_
  have hk := isGrpPullback_pullback B y
  have hkU := hk.comp hpb
  obtain ⟨⟨c, hc⟩, hprin⟩ := GlobalTheory.siegPre_pullback g n o ζ F.X (Sp K) F.s ((y ≫ T) ≫ F.s) (y ≫ T) F.univ rfl
  have hcp := hprin c hc F.princ
  obtain ⟨φc, φc₂, hcpb, hcsq, hcP, -⟩ := hc
  obtain ⟨L₀, h₀, hlam₀, ha₀⟩ := PolBundleLoc.exists_ample_root c.A c.ab c.isLB c.rig₁ c.rig₂ c.symm hcp.1
  have hk₀ := KTrivOfLam.kTriv_of_lam_iso _ c.A c.ab c.P c.isLB hcp.2 L₀ h₀ hlam₀
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hcpb hkU
  haveI := he
  let ψ : c.A.left ⟶ B.left := e.hom.left ≫ pullback.fst B.hom y
  have hψ : IsGrpPullback c.A B y ψ := by
    have := (isGrpPullback_of_iso e).comp hk
    rwa [Category.id_comp] at this
  obtain ⟨ψ₂, sψ⟩ := SiegPull.exists_isSquare hψ.1.w
  have hN : (L.pull ψ).IsLB := pull_isLB hL ψ
  have hlamN : LBIso (abelian₂ c.A (L.pull ψ)) ((abelian₂ B L).pull ψ₂) :=
    SiegPull.lbIso_lam_pull hψ ((CechPic.cls_eq_iff hN hN).1 rfl) sψ
  have hsq' : IsSquare (ψ ≫ β) (ψ₂ ≫ β₂) := SiegPull.isSquare_comp sψ hsq
  have hφ : ψ ≫ β = φc := by simpa [ψ, Category.assoc] using heφ
  have e₂ : ψ₂ ≫ β₂ = φc₂ := SiegPull.isSquare_unique hsq' hcsq hφ
  have hpullP : LBIso ((abelian₂ B L).pull ψ₂) (F.univ.P.pull (ψ₂ ≫ β₂)) := SiegPull.lbIso_pull_comp hiso ψ₂
  rw [e₂] at hpullP
  have iLN : (abelian₂ c.A (L.pull ψ)).IsLB := LB.isLB_linComb hN _ _
  have iL0 : (abelian₂ c.A L₀).IsLB := LB.isLB_linComb h₀ _ _
  have iLB : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hlam : CechPic.lam (CechPic.cls (L.pull ψ) hN) (fst c.A c.A) (snd c.A c.A) =
      CechPic.lam (CechPic.cls L₀ h₀) (fst c.A c.A) (snd c.A c.A) :=
    (CechPic.cls_cube_two hN _ _ iLN).symm.trans
      (((CechPic.cls_eq_iff iLN (pull_isLB iLB _)).2 hlamN).trans
        (((CechPic.cls_eq_iff (pull_isLB iLB _) (pull_isLB F.univ.isLB _)).2 hpullP).trans
          (((CechPic.cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).2 hcP).symm.trans
            (((CechPic.cls_eq_iff iL0 c.isLB).2 hlam₀).symm.trans (CechPic.cls_cube_two h₀ _ _ iL0)))))
  obtain ⟨hampN, -⟩ := AmpleKerFibre.relAmple_kTriv_of_lam_eq K c.A c.ab L₀ h₀ ha₀ hk₀ (L.pull ψ) hN hlam
  have : IsProper c.A.hom := c.ab.proper
  have hAN := (relAmple_iff_isAmpleLB_of_isAffine c.A hN).1 hampN
  haveI : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have h1 := hAN.pull_of_isAffineHom e.inv.left
  have h2 : LBIso ((L.pull ψ).pull e.inv.left) (L.pull (pullback.fst B.hom y)) := by
    have h3 := SiegPull.lbIso_pull_comp ((CechPic.cls_eq_iff hN hN).1 rfl) e.inv.left
    have ee : e.inv.left ≫ ψ = pullback.fst B.hom y := by
      simp only [ψ]
      rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
    rwa [ee] at h3
  exact (isAmpleLB_congr (pull_isLB hN _) (pull_isLB hL _) h2).1 h1

end GlobalTheory.MumAmple
