import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleDescendsAlongIsogenyTorsorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareDescent

theorem descends : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A']
    [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A →
    IsAbelianScheme A' → IsAbelianScheme B → IsDual A B P → IsMonHom i → IsMonHom q → IsFinite q.left →
    Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → Triv (ev P (fst N B ≫ i) (snd N B)) →
    ∃ P' : LB (A' ⊗ B).left, P'.IsLB ∧ IsAdditive P' ∧ LBIso (ev P' (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hD hi hq hfin hfl hsurj hker hN
  obtain ⟨P₀, hP₀, e⟩ := GlobalTheory.T.additive_lineBundle_descends_along_isogeny_torsor K A A' B N P i q hA hA' hB hD.isLB hD.additive hD.zero hi hq hfin hfl
    hsurj (torsor_square i q hker) hN
  have key : ∀ (Y : Over (Sp K)) (a : Y ⟶ A) (b : Y ⟶ B), evc hP₀ (a ≫ q) b = evc hD.isLB a b := by
    intro Y a b
    have c := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff (pull_isLB hP₀ _) hD.isLB).2 e)
    rw [cls_ev hP₀, pull_evc, lift_fst_assoc, lift_snd] at c
    exact c
  let φ : Fin 2 → ((A' ⊗ B).left ⟶ (A' ⊗ B).left) :=
    ![(lift (fst A' B) (snd A' B)).left, (lift (fst A' B) (1 : A' ⊗ B ⟶ B)).left]
  have hP' : (LB.LinComb P₀ φ ![1, -1]).IsLB := LB.isLB_linComb hP₀ _ _
  have ev' : ∀ (Y : Over (Sp K)) (a : Y ⟶ A') (b : Y ⟶ B), evc hP' a b = evc hP₀ a b - evc hP₀ a 1 := by
    intro Y a b
    rw [evc, cls_linComb hP₀, Fin.sum_univ_two, map_add, map_zsmul, map_zsmul, ← pull_comp, ← pull_comp]
    simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd, MonObj.comp_one, one_smul, neg_smul, evc, sub_eq_add_neg]
  have one : ∀ (Y : Over (Sp K)) (b : Y ⟶ B), evc hP₀ (1 : Y ⟶ A') b = 0 := fun Y b ↦ by
    have : (1 : Y ⟶ A) ≫ q = 1 := by simp
    rw [← this, key]
    exact hD.additive.evc_one hD.isLB b
  refine ⟨_, hP', CubeNoeth.isAdditive_of_triv_axes hA' hB hP' ?_ ?_, ?_⟩
  · rw [triv_ev_iff hP', ev', one, one, sub_self]
  · rw [triv_ev_iff hP', ev', sub_self]
  · refine (cls_eq_iff (pull_isLB hP' _) hD.isLB).1 ?_
    rw [cls_ev hP', ev', key, key, evc_one_right hD.isLB hD.zero, sub_zero, evc, lift_fst_snd, Over.id_left,
      pull_id]

end GlobalTheory.PoincareDescent
