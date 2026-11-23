import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLineBundlePullbackOfTranslates
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_lineBundle_pullback_of_translates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (c : Pic A.left) (V : A.left.Opens), cls L hL = c → IsAffineOpen V → IsLocus c V → ∀ (T : Over (Sp R)) [IsAffine T.left] (n : ℕ) (a : Fin n → (T ⟶ A)), ⨆ i, ((fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ → (∀ i, GlobalTheory.CechPic.pull (a i).left c + GlobalTheory.CechPic.pull ((a i)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0) → GlobalTheory.IsAmpleLB (L.pull (fst A T).left) := by
  first | exact @GlobalTheory.isAmpleLB_pull_fst_of_translates | exact GlobalTheory.isAmpleLB_pull_fst_of_translates | (intros; apply GlobalTheory.isAmpleLB_pull_fst_of_translates <;> assumption)
