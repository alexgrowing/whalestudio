import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.RigidifyTwist

theorem rigidified_sym_lam_twist : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (M : LB A.left) (hM : M.IsLB), Out.Sym A M → ∃ (M' : LB A.left) (hM' : M'.IsLB), Out.Rigidified A M' ∧ Out.Sym A M' ∧ lam (cls M' hM') (fst A A) (snd A A) = lam (cls M hM) (fst A A) (snd A A) := by
  intro S A _ M hM hs
  have hM' := LB.isLB_linComb hM (K := Fin 2) ![𝟙 A.left, A.hom ≫ eSec A] ![1, -1]
  have hc : cls _ hM' = cls M hM - CechPic.pull (A.hom ≫ eSec A) (cls M hM) := by
    rw [CechPic.cls_linComb hM, Fin.sum_univ_two]
    simp [CechPic.pull_id, sub_eq_add_neg]
  have hz : ∀ {T : Over S} (z : T ⟶ A), CechPic.pull z.left (CechPic.pull (A.hom ≫ eSec A) (cls M hM)) =
      CechPic.pull (T.hom ≫ eSec A) (cls M hM) := by
    intro T z
    rw [← CechPic.pull_comp, ← Category.assoc, Over.w z]
  refine ⟨_, hM', ?_, ?_, ?_⟩
  · refine (CechPic.cls_eq_zero_iff (pull_isLB hM' _)).1 ?_
    rw [CechPic.cls_pull hM', hc, map_sub, ← CechPic.pull_comp, sub_eq_zero]
    exact congrArg (fun f => CechPic.pull f (cls M hM))
      ((Category.id_comp _).symm.trans (((Over.w η[A]).symm =≫ _).trans (Category.assoc _ _ _)))
  · intro s
    obtain ⟨U, hU, t, ht⟩ := hs s
    refine ⟨U, hU, (CechPic.cls_eq_zero_iff (LB.isLB_linComb hM' _ _)).1 ?_⟩
    have h0 := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 ⟨t, ht⟩
    have hinv : ∀ {Z : Scheme.{0}} (f : S ⟶ Z), (GrpObj.inv : A ⟶ A).left ≫ A.hom ≫ f = A.hom ≫ f := by
      intro Z f; rw [← Category.assoc, Over.w]
    rw [CechPic.cls_linComb hM, Fin.sum_univ_two] at h0
    rw [CechPic.cls_linComb hM', Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul,
      hc, map_sub, ← CechPic.pull_comp, Category.assoc, hinv] at h0 ⊢
    rw [← h0]; abel
  · simp only [CechPic.lam, hc, map_sub, hz]
    abel

end GlobalTheory.RigidifyTwist
