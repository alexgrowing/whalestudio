import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomZarhinProductToEighthPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivialStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic

theorem principal_zP : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Out.RelAmple (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) ∧ ∀ (T : Over S) (x : T ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → x = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hunit hK
  refine ⟨?_, fun T x hx => ?_⟩
  · have hAb : IsAbelianScheme (Zob c.A B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _
      (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
    have := hAb.proper
    have hA : Out.RelAmple c.A c.diag := hK.1
    have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ Out.powObj c.A 8,
        ∀ u, x ≫ Out.powPr c.A u = y u := fun T y =>
      ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
        fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
    have h8 := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef GlobalTheory.SemiRigid.globalFns h M 8 _ _ S t c
      (Out.powObj c.A 8) (Out.powPr c.A) (zW d) (fun u => inferInstance) huniv hA (GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef d hd)
    have := GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower h M d S t c B Q la mu hZ hd hunit
    have hF : (LB.LinComb c.P (K := Fin 8 × Fin 8)
        (fun uv => (lift (Out.powPr c.A uv.1) (Out.powPr c.A uv.2)).left) (fun uv => zW d uv.1 uv.2)).IsLB :=
      LB.isLB_linComb c.isLB _ _
    have hp := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom (zphi c.A B mu) hF h8
    have hzP := zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
    refine GlobalTheory.PosDefAmple.relAmple_of_nsmul (pull_isLB hzP _) (pull_isLB hF _) (N := d) hd ?_ hp
    rw [cls_pull hzP, cls_zP, cls_pull hF, cls_linComb c.isLB, GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form h M d S t c B Q la mu hZ hd, map_sum]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, zphi_powPr, zphi_powPr]
  · have hla := hZ.2.2.2.1
    have hmu := hZ.2.2.2.2.1
    let f : (T ⟶ c.A) →* (T ⟶ B) := MonoidHom.mk' (fun a => a ≫ la) (fun a b => MonObj.mul_comp a b la)
    let g : (T ⟶ B) →* (T ⟶ c.A) := MonoidHom.mk' (fun a => a ≫ mu) (fun a b => MonObj.mul_comp a b mu)
    have hfg : ∀ a, g (f a) = a ^ d := fun a => by
      change (a ≫ la) ≫ mu = a ^ d
      rw [Category.assoc, hZ.2.2.2.2.2.1, MonObj.comp_pow, Category.comp_id]
    obtain ⟨hu, hv⟩ := GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial d (T ⟶ c.A) (T ⟶ B) f g hd hfg (fun i => x ≫ pa c.A B i) (fun j => x ≫ pb c.A B j)
      (fun i => by simpa [f, Category.assoc] using GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations h M d S t c B Q la mu hZ T x hx i)
      (fun j => GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations h M d S t c B Q la mu hZ T x hx j)
      (GlobalTheory.T.zarhinBundle_kernel_of_secondCoord_trivial h M d S t c B Q la mu hZ T x hx)
    have e1 : x ≫ fst _ _ = 1 := (Out.powIsLimit c.A 4).hom_ext fun ⟨i⟩ => by
      change (x ≫ fst _ _) ≫ Out.powPr c.A i = 1 ≫ Out.powPr c.A i
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hu i)
    have e2 : x ≫ snd _ _ = 1 := (Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by
      change (x ≫ snd _ _) ≫ Out.powPr B j = 1 ≫ Out.powPr B j
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hv j)
    ext1
    · rw [e1, MonObj.one_comp]
    · rw [e2, MonObj.one_comp]

end GlobalTheory.ZarhinFam
