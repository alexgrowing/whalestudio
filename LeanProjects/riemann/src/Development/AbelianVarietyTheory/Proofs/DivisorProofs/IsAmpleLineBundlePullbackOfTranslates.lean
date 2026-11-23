import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAddInfPreimageSubGrpSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateMulInvIsNonvanishingLocusSquareStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isAmpleLB_pull_fst_of_translates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (c : Pic A.left) (V : A.left.Opens), cls L hL = c → IsAffineOpen V → IsLocus c V → ∀ (T : Over (Sp R)) [IsAffine T.left] (n : ℕ) (a : Fin n → (T ⟶ A)), ⨆ i, ((fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ → (∀ i, GlobalTheory.CechPic.pull (a i).left c + GlobalTheory.CechPic.pull ((a i)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0) → GlobalTheory.IsAmpleLB (L.pull (fst A T).left) := by
  intro R _ _ A _ hA L hL c V hc hV hloc T _ n a hcov hrel
  haveI : IsProper A.hom := hA.proper
  have hL' : (L.pull (fst A T).left).IsLB := LB.isLB_pull hL _
  have h2 : (lbPow (L.pull (fst A T).left) 2).IsLB := GlobalTheory.isLB_lbPow hL' 2
  have hcls : cls _ h2 = 2 • CechPic.pull (fst A T).left c := by
    rw [cls_lbPow hL' 2 h2, cls_pull hL _ hL', hc]
  have hsec : ∀ i, ∃ s : (lbPow (L.pull (fst A T).left) 2).Sec, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s =
      (fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V := fun i =>
    IsLocus.exists_sec h2 (hcls ▸ GlobalTheory.T.translate_mul_inv_isNonvanishingLocus_square (Sp R) A hA c V hloc T (a i) (hrel i))
  choose s hs using hsec
  exact isAmpleLB_of_cover hL' (by norm_num) s (by simp only [hs]; exact hcov)
    fun i => (hs i).symm ▸ GlobalTheory.T.isAffineOpen_preimage_add_inf_preimage_sub_grpScheme R A V hV T (a i)

end GlobalTheory
