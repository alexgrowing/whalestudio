import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LineQuot

set_option backward.isDefEq.respectTransparency false in

theorem exists_taut_quot : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (φ : T ⟶ PSpace k N) (L : T.Modules), IsVB L 1 → ∃ (Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB Q 1 ∧ JointEpi s ∧ Rel φ s := by
  intro k _ N T φ L hL
  have hM : ((ProjSpace.O1 k N).pull φ).IsLB := LB.isLB_pull (ProjSpace.O1_isLB k N) φ
  refine ⟨twist L ((ProjSpace.O1 k N).pull φ),
    fun j => Twist.secHom L (Cartier.secPull (ProjSpace.coord k N j) φ), hL.twist hM, ?_, ?_⟩
  · intro Z a ha
    have hc := ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord k N) φ
    ext V q
    refine Twist.sec_ext_of_cover
      (fun j => V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ)) (fun _ => inf_le_left)
      (GlobalTheory.LB.le_iSup_inf hc V) fun j => ?_
    rw [← Twist.app_resM, ← Twist.app_resM]
    obtain ⟨t, ht⟩ := (Twist.bijective_secHom_app (F := L) hM (Cartier.secPull (ProjSpace.coord k N j) φ)
      (V := V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ)) inf_le_right).2
      (Twist.resM _ inf_le_left q)
    rw [← ht]
    have e := congrArg (fun m => (Scheme.Modules.Hom.app m (V ⊓ Out.nonzeroLocus (Cartier.secPull (ProjSpace.coord k N j) φ))) t) (ha j)
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e
    rw [e]
    simp
  · intro i j W h t
    have hW : W ≤ ((ProjSpace.O1 k N).pull φ).U (fun _ => i) := h.trans (Cartier.pull_U (ProjSpace.O1 k N) φ fun _ => i).ge
    apply (Twist.chartEquiv hM (fun _ => i) hW).injective
    rw [LinearEquiv.map_smul, Twist.chartEquiv_secHom_app, Twist.chartEquiv_secHom_app,
      ProjSpace.resG_secPull_coord, ProjSpace.resG_secPull_coord, ProjSpace.pullRatio_self, one_smul]

end GlobalTheory.LineQuot

end
