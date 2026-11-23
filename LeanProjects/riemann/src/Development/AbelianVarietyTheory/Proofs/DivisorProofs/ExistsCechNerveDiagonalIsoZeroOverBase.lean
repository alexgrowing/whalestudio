import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

noncomputable def cechDiagApp {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    yoneda.obj Y ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (by intro; exact Category.id_comp _)

@[reassoc (attr := simp)]
theorem cechDiagApp_π {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) (j : Fin (k + 1)) :
    cechDiagApp f k ≫ WidePullback.π _ j = 𝟙 _ := WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
theorem cechDiagApp_base {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    cechDiagApp f k ≫ WidePullback.base _ = yoneda.map f := WidePullback.lift_base _ _ _ _

noncomputable def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := cechDiagApp f n.unop.len
  naturality n m g := by
    change 𝟙 (yoneda.obj Y) ≫ cechDiagApp f m.unop.len = cechDiagApp f n.unop.len ≫ _
    rw [Category.id_comp]
    apply WidePullback.hom_ext
    · intro j
      rw [cechDiagApp_π]
      erw [Category.assoc, WidePullback.lift_π]
      exact (cechDiagApp_π f _ _).symm
    · rw [cechDiagApp_base]
      refine Eq.trans ?_ (Category.assoc (cechDiagApp f _) ((cech f).map g) _).symm
      erw [WidePullback.lift_base]
      exact (cechDiagApp_base f _).symm

theorem cechDiag_spec {Y X : Scheme.{0}} (f : Y ⟶ X) :
    ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  refine ⟨cechDiag f, ?_, ?_⟩
  · refine ⟨⟨(WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 : _ ⟶ yoneda.obj Y), ?_, ?_⟩⟩
    · exact cechDiagApp_π f 0 0
    · change WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 ≫ cechDiagApp f 0 = 𝟙 _
      apply WidePullback.hom_ext
      · intro j
        rw [Fin.fin_one_eq_zero j, Category.assoc, cechDiagApp_π, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, cechDiagApp_base, Category.id_comp, WidePullback.π_arrow]
  · ext n : 1
    exact cechDiagApp_base f _

end GlobalTheory.EtC.GmStep
