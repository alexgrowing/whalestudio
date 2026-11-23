import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixLocal

open GlobalTheory.CechPic

theorem lbIso_pull_of_local : ∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left) := by
  intro H A B _ _ _ _ L M Φ hΦ hA _ hL hM rL rM loc
  haveI := hΦ
  refine GlobalTheory.ThetaAffineGlue.lbIso_of_local GlobalTheory.SemiRigid.globalFns A hA hL (pull_isLB hM Φ.left) rL ?_ loc
  refine (GlobalTheory.PolProd.rigidified_iff A (pull_isLB hM Φ.left)).2 ?_
  rw [cls_pull hM, ← pull_comp, GlobalTheory.PolProd.eSec_comp Φ]
  exact (GlobalTheory.PolProd.rigidified_iff B hM).1 rM

end GlobalTheory.HomFixLocal
