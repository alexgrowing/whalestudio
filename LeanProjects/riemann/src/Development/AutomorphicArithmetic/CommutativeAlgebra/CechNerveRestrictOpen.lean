import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

private theorem cechNerve_level_isPullback {C : Type*} [Category C] {a b : Arrow C}
    [∀ n : ℕ, HasWidePullback a.right (fun _ : Fin (n + 1) => a.left) fun _ => a.hom]
    [∀ n : ℕ, HasWidePullback b.right (fun _ : Fin (n + 1) => b.left) fun _ => b.hom]
    (F : a ⟶ b) (h : IsPullback F.left a.hom b.hom F.right) (n : SimplexCategoryᵒᵖ) :
    IsPullback ((Arrow.mapCechNerve F).app n) (WidePullback.base _) (WidePullback.base _) F.right := by
  have hc : (Arrow.mapCechNerve F).app n ≫ WidePullback.base _ = WidePullback.base _ ≫ F.right := by
    simp [Arrow.mapCechNerve]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc
    (fun s => WidePullback.lift s.snd
      (fun i => h.lift (s.fst ≫ WidePullback.π _ i) s.snd (by
        simp only [Category.assoc, WidePullback.π_arrow]
        simpa using s.condition)) (by simp)) ?_ ?_ ?_⟩⟩
  · intro s
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · simp [Arrow.mapCechNerve]
    · simpa [Arrow.mapCechNerve] using s.condition.symm
  · intro s
    simp
  · intro s m h1 h2
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · simp only [WidePullback.lift_π]
      refine h.hom_ext ?_ ?_
      · rw [h.lift_fst, ← h1]
        simp [Arrow.mapCechNerve]
      · rw [h.lift_snd, ← h2, Category.assoc]
        simp
    · simpa using h2

private theorem comp_eq_of_comp_inv {C : Type*} [Category C] {A B D E : C} {i : A ⟶ B} {ψ : B ⟶ D} {t : A ⟶ E}
    (e : E ≅ D) (h : i ≫ ψ ≫ e.inv = t) : i ≫ ψ = t ≫ e.hom := by
  rw [← h]
  simp

theorem UpperTheory.cech_nerve_restrict_open :
    ∀ {V Y : Scheme.{0}} (f : V ⟶ Y) (W : Y.Opens), ∃ ψ : cech (f ∣_ W) ⟶ cech f, ψ ≫ cechAug f = cechAug (f ∣_ W) ≫ sch.map W.ι ∧
      ∀ (p : ℕ) (Z : Scheme.{0}) (g : Z ⟶ Y) (e : yoneda.obj Z ≅ (cech f).obj (op (SimplexCategory.mk p))), e.hom ≫ (cechAug f).app (op (SimplexCategory.mk p)) = yoneda.map g →
        ∃ e' : yoneda.obj (g ⁻¹ᵁ W : Scheme.{0}) ≅ (cech (f ∣_ W)).obj (op (SimplexCategory.mk p)), e'.hom ≫ ψ.app (op (SimplexCategory.mk p)) = yoneda.map (g ⁻¹ᵁ W).ι ≫ e.hom := by
  intro V Y f W
  have hP0 := isPullback_morphismRestrict f W
  have hP1 := hP0.map yoneda
  let F : Arrow.mk (yoneda.map (f ∣_ W)) ⟶ Arrow.mk (yoneda.map f) :=
    Arrow.homMk (yoneda.map (f ⁻¹ᵁ W).ι) (yoneda.map W.ι) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, morphismRestrict_ι])
  have hF : IsPullback F.left (Arrow.mk (yoneda.map (f ∣_ W))).hom (Arrow.mk (yoneda.map f)).hom F.right :=
    hP1.flip
  have hL := cechNerve_level_isPullback F hF
  refine ⟨Arrow.mapCechNerve F, ?_, ?_⟩
  · exact NatTrans.ext (funext fun n => (hL n).w)
  · intro p Z g e he
    have hA := ((isPullback_morphismRestrict g W).map yoneda).flip
    have hL' : IsPullback ((Arrow.mapCechNerve F).app (op (SimplexCategory.mk p)) ≫ e.inv)
        ((cechAug (f ∣_ W)).app (op (SimplexCategory.mk p))) (yoneda.map g) (yoneda.map W.ι) :=
      IsPullback.of_iso (hL (op (SimplexCategory.mk p))) (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
        (by simp) (by simp; rfl) (by
          simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
          exact (Iso.eq_inv_comp e).2 he) (by simp; rfl)
    refine ⟨hA.isoIsPullback _ _ hL', ?_⟩
    have h1 := hA.isoIsPullback_hom_fst _ _ hL'
    exact comp_eq_of_comp_inv e h1

end
