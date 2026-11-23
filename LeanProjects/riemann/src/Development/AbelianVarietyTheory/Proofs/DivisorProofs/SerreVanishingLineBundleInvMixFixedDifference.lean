import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open GlobalTheory.AbLaw GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem exists_not_NV_mix (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A]
    (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L) (d : ℤ) :
    ∃ N : ℕ, ∀ a b : ℕ, N ≤ a + b → (a : ℤ) - b = d → ∀ j : ℕ, ¬ NV A (mix A L a b) (j + 1) := by
  have := hA.proper
  letI := algebraΓOfHom A.hom
  have hLa : IsAmpleLB L := isAmpleLB_of_relAmple_of_isAffine A hL hamp
  have hι : IsIso (GrpObj.inv : A ⟶ A) := ⟨⟨GrpObj.inv, by simp, by simp⟩⟩
  have : IsIso (GrpObj.inv : A ⟶ A).left := (Over.forget _).map_isIso GrpObj.inv
  have hinv : IsAmpleLB (L.pull (GrpObj.inv : A ⟶ A).left) := hLa.pull_of_isAffineHom _
  have hM : (mix A L 1 1).IsLB := LB.isLB_linComb hL _ _
  have hMa : IsAmpleLB (mix A L 1 1) := by
    refine hLa.tensor hinv hM ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hM hL) (LB.isLB_pull hL _))).1 ?_)
    unfold mix at hM ⊢
    rw [cls_div (LB.isLB_div hM hL) (LB.isLB_pull hL _), cls_div hM hL, cls_pull hL,
      cls_linComb hL]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, one_smul]
    abel
  have hP : (mix A L d 0).IsLB := LB.isLB_linComb hL _ _
  have hF := Twist.isFiniteQC_twist (F := structureModule A.left) hP
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (hMa.eventually_subsingleton_coh_twistZ (f := A.hom) (fun _ => rfl) (twist (structureModule A.left) (mix A L d 0)))
  have hsep : A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from A.hom]
    infer_instance
  refine ⟨(2 * n₀ + d).toNat, fun a b hN hd j ⟨κ, _, _, W, hW, hc, hne⟩ => hne ?_⟩
  have hI : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, W i) := fun s hs =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hs) fun i _ => hW i
  have hQ : (mix A L a b).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨e⟩ := FieldChangeInter.nonempty_coh_equiv A.hom hQ hc hI (j + 1)
  obtain ⟨e₂⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule A.left) hP
    (Twist.isLB_lbZPow hM b) hQ (by
      rw [cls_lbZPow hM]
      unfold mix at hP hQ hM ⊢
      rw [cls_linComb hL, cls_linComb hL, cls_linComb hL]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, one_smul, zero_smul, add_zero]
      have ha : (a : ℤ) = d + b := by omega
      rw [ha, add_smul, smul_add]
      abel)
  haveI := hn₀ b (by omega) (j + 1) j.succ_pos
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  exact (e.trans (cohOn.mapIso K ⊤ (j + 1) e₂).symm).injective.subsingleton

end GlobalTheory.AmpleGen
