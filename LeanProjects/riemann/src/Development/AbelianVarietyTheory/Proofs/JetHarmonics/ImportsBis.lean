import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVRStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.BoxSectionValues

open GlobalTheory.FieldBaseChange GlobalTheory.BoxExpansion

set_option maxHeartbeats 1000000 in

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (A A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G G' : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif (maximalIdeal V) D' A' G') (U : Unif (maximalIdeal V) D A G) (PU : UnifPowOf3 pD pA pG U' U) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (σ : Fin j → U.SecGF F k) (s : Fin j → Fam D.toPre F k) (σ' : U'.SecGF F k) (S : Fam D'.toPre F k), (∀ i, U.ExpandsG F k (σ i) (s i)) → IsBoxFam pD F k S s → U'.ExpandsG F k σ' S → ∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (R := V) (G := G') F).left) (ri : Fin j → (Z ⟶ (UnifPre.GF (R := V) (G := G) F).left)), (∀ i, ri i ≫ UnifPre.gFK (G := G) F = r ≫ UnifPre.gFK (G := G') F ≫ (pG.pr i).left) → (∀ i, ri i ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = r ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left) → ∀ (z : Z) (J J'), Good U.LG.L z J → Good U'.LG.L z J' → (bw PU.wL (r ≫ UnifPre.gFK (G := G') F) z (fun i => J ((r ≫ UnifPre.gFK (G := G') F) ≫ (pG.pr i).left)) (J' (r ≫ UnifPre.gFK (G := G') F)) ^ k).val * sval σ' r z J' = ∏ i, sval (σ i) (ri i) z J := by
  intro h₁ h₂ h₄ hT V _ _ _ _ j D D' A A' G G' _ _ _ _ pD pA pG U' U P F _ _ k hk t s t' S hE hS hE' Z r ri hr₁ hr₂
    z J J' hJ hJ'
  classical
  choose n c σ f hA hs hf using hE
  let e := (Fintype.equivFin (∀ i, Fin (n i))).symm
  let σ' := fun l => boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k (fun i => σ i (e l i))
  obtain ⟨s', hs'⟩ := exists_secLin U'.LG.isLB (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left
    (UnifPre.gFK (G := G') F) (fun _ : Fin 1 => UnifPre.gFK (G := G') F) (fun _ => (Category.comp_id _).symm) σ'
    (fun l => (1 : F) * ∏ i, c i (e l i))
  have hX : U'.ExpandsG F k s' ((1 : F) • S) := by
    refine ⟨_, _, σ', fun l => boxFamB pD k (fun i => f i (e l i)), fun l ee => ?_, hs', fun α' => ?_⟩
    · exact expandsAt_box' P k ee _ _ (fun i => hA i (e l i) ee) _ _
        (isBoxSecG_boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k _) (isBoxFamB_boxFamB pD k _)
    · obtain ⟨hφ, hb⟩ := hS α'
      refine secLin_box e (1 : F) c D.toPre.P.isLB D'.toPre.P.isLB pD.w
        (p := prB pD F) (q := fun i => (pD.pw.pr i).left) (GC.famφ_eq D'.toPre F α') (fun i => ?_) (fun i => ?_)
        (S.s α') _ (fun i => (s i).s (pD.xe α' i)) (fun i a => f i a (pD.xe α' i)) _ (fun _ => rfl)
        (fun y J J' hJ hJ' => box_val pD.w hφ _ _ _ hb (𝟙 _) y hJ hJ') (fun l y J J' hJ hJ' => ?_)
        (fun i => hf i (pD.xe α' i))
      · exact congrArg (fun q => q.left) (whiskerLeft_snd (TF (R := V) F) (pD.pw.pr i)).symm
      · exact congrArg (fun q => q.left) (whiskerLeft_fst (TF (R := V) F) (pD.pw.pr i))
      · obtain ⟨hψ, H⟩ := isBoxFamB_boxFamB pD k (fun i => f i (e l i)) α'
        exact box_val pD.w hψ _ _ _ H _ y hJ hJ'
  rw [one_smul] at hX
  obtain rfl : t' = s' := ((GlobalTheory.T.groupExpansion_bijective_of_completeDVR h₁ h₂ h₄ hT V D' A' G' U' F k hk).2 S).unique hE' hX
  have a₂ := fun l => boxG_val (isBoxSecG_boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k (fun i => σ i (e l i)))
    (r ≫ UnifPre.gFK (G := G') F) z hJ hJ'
  have a₃ : ∀ i, sval (t i) (ri i) z J = ∑ a, constHomVal (r ≫ (fst (TFK (R := V) F)
      ((Over.pullback (jK V)).obj G')).left) z (c i a) *
        sval (σ i a) ((r ≫ UnifPre.gFK (G := G') F) ≫ (pG.pr i).left) z J := fun i => by
    refine (secLin_val (hs i) (ri i) z hJ).trans (Finset.sum_congr rfl fun a _ => ?_)
    rw [hr₁ i, ← Category.assoc]
    exact congrArg (· * _) ((gs_scal _ _ z _).trans ((congrArg (fun q => constVal q z (c i a)) (hr₂ i)).trans
      (constVal_eq _ _ _)))
  have a₄ : sval t' r z J' = ∑ l, constHomVal (r ≫ (fst (TFK (R := V) F)
      ((Over.pullback (jK V)).obj G')).left) z (1 * ∏ i, c i (e l i)) *
        sval (σ' l) (r ≫ UnifPre.gFK (G := G') F) z J' := by
    refine (secLin_val hs' r z hJ').trans (Finset.sum_congr rfl fun a _ => ?_)
    exact congrArg (· * _) ((gs_scal _ _ z _).trans (constVal_eq _ _ _))
  have a₅ := prod_sum_reindex (constHomVal (r ≫ (fst (TFK (R := V) F)
      ((Over.pullback (jK V)).obj G')).left) z) e 1 c
      (fun i a => sval (σ i a) ((r ≫ UnifPre.gFK (G := G') F) ≫ (pG.pr i).left) z J)
  rw [map_one, _root_.one_mul] at a₅
  rw [Finset.prod_congr rfl fun i _ => a₃ i, ← a₅, a₄, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← a₂ l, mul_left_comm]

end GlobalTheory.BoxSectionValues
