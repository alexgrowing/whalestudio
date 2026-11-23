import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisAltLast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ElRep

theorem sq_ext {S : Scheme.{0}} (A : Over S) {X : Scheme.{0}} (f g : X ⟶ (A ⊗ A).left)
    (h₁ : f ≫ (fst A A).left = g ≫ (fst A A).left) (h₂ : f ≫ (snd A A).left = g ≫ (snd A A).left) : f = g :=
  pullback.hom_ext h₁ h₂

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) := by
  intro S A _ _ Q hQ O _ bar r e W d hbar hspan hW hd hsum T t A' _ _ φ' φ₂' B' _ φB pr' hApb hsq hBpb hpr' hprφ
    huniq act hact hadj Φ hΦ
  have hQ' : QHyp A' (Q.pull φ₂') := GlobalTheory.T.symmetricBiextensionHyp_pullback_of_groupPullback S T t A A' φ' φ₂' Q hApb hsq hQ
  obtain ⟨hA', hL', g₁, g₂, hsym', hamp'⟩ := hQ'
  have C := GlobalTheory.CasimirPull.main T A' (Q.pull φ₂') hA' hL' g₁ g₂ hsym' hamp' O bar r e W d hbar hspan hW hd hsum
    act hact hadj B' pr' hpr' huniq Φ hΦ
  have hQL : Q.IsLB := hQ.2.1
  have e₁ : ∀ u v : Fin r, (lift (pr' u) (pr' v)).left ≫ φ₂' =
      φB ≫ (lift (Out.powPr A (n := r) u) (Out.powPr A (n := r) v)).left := fun u v => by
    apply sq_ext A
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hprφ, Category.assoc,
        ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hprφ, Category.assoc,
        ← Over.comp_left, lift_snd]
  have e₂ : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂' = φ' ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply sq_ext A
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp,
        Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp,
        Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id]
  have C' := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB (LB.isLB_linComb hL' _ _) _) (LB.isLB_linComb hL' _ _)).2 C
  rw [GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hL' _ _), GlobalTheory.CechPic.cls_linComb hL', GlobalTheory.CechPic.cls_linComb hL',
    GlobalTheory.CechPic.cls_pull hQL] at C'
  simp only [map_sum, map_zsmul, ← GlobalTheory.CechPic.pull_comp, Category.assoc, e₁, e₂] at C'
  unfold diagPow formLB
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB (LB.isLB_linComb hQL _ _) _)
    (pull_isLB (pull_isLB (LB.isLB_linComb hQL _ _) _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hQL _ _), GlobalTheory.CechPic.cls_pull (pull_isLB (LB.isLB_linComb hQL _ _) _),
    GlobalTheory.CechPic.cls_pull (LB.isLB_linComb hQL _ _), GlobalTheory.CechPic.cls_linComb hQL, GlobalTheory.CechPic.cls_linComb hQL]
  simp only [map_sum, map_zsmul, ← GlobalTheory.CechPic.pull_comp, Category.assoc]
  exact C'.symm

end GlobalTheory.ElRep
