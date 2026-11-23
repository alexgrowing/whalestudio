import Development.EtaleCohomology.EtaleSheaves.CxDescPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.shiftPf

theorem conj_iff {α β γ δ : Type*} (F : α → β) (G : γ → δ) (e1 : α ≃ γ) (e2 : β ≃ δ)
    (h : ∀ x, G (e1 x) = e2 (F x)) :
    (Function.Bijective F ↔ Function.Bijective G) ∧ (Function.Injective F ↔ Function.Injective G) := by
  have hG : G = e2 ∘ F ∘ e1.symm := funext fun y => by simpa using h (e1.symm y)
  have hF : F = e2.symm ∘ G ∘ e1 := funext fun x => by simp [h]
  refine ⟨⟨fun hb => ?_, fun hb => ?_⟩, ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · rw [hG]; exact e2.bijective.comp (hb.comp e1.symm.bijective)
  · rw [hF]; exact e2.symm.bijective.comp (hb.comp e1.bijective)
  · rw [hG]; exact e2.injective.comp (hb.comp e1.symm.injective)
  · rw [hF]; exact e2.symm.injective.comp (hb.comp e1.injective)

section Cat
variable {C : Type*} [Category C]

abbrev pre {X X' : C} (u : X ⟶ X') (Y : C) : (X' ⟶ Y) → (X ⟶ Y) := fun h => u ≫ h

theorem pre_conj {W W' X X' : C} (u' : W ⟶ W') (u : X ⟶ X') (a : W ≅ X) (b : W' ≅ X')
    (h : u' ≫ b.hom = a.hom ≫ u) (Y : C) :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u' Y)) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u' Y)) :=
  conj_iff _ _ ((Iso.homCongr b.symm (Iso.refl Y))) ((Iso.homCongr a.symm (Iso.refl Y))) (fun x => by
    simp only [pre, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, h, Category.assoc])

theorem pre_target {X X' Y Y' : C} (u : X ⟶ X') (e : Y ≅ Y') :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u Y')) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u Y')) :=
  conj_iff _ _ (Iso.homCongr (Iso.refl X') e) (Iso.homCongr (Iso.refl X) e) (fun x => by
    simp [pre, Iso.homCongr_apply])

theorem pre_shift [HasShift C ℤ] {X X' : C} (u : X ⟶ X') (p : ℤ) (Y : C) :
    (Function.Bijective (pre (u⟦p⟧') Y) ↔ Function.Bijective (pre u (Y⟦-p⟧))) ∧
      (Function.Injective (pre (u⟦p⟧') Y) ↔ Function.Injective (pre u (Y⟦-p⟧))) :=
  conj_iff _ _ ((shiftEquiv C p).toAdjunction.homEquiv X' Y) ((shiftEquiv C p).toAdjunction.homEquiv X Y) (fun x => by
    simp only [pre]
    exact ((shiftEquiv C p).toAdjunction.homEquiv_naturality_left u x).symm)

end Cat

variable {R : Type} [CommRing R]

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

theorem toHom_cpull {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    CohomologyClass.toHom (cpull f I n x) = (Qt R).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  rw [cpull, cpre_mk, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp,
    ← Cocycle.equivHomShift_symm_precomp]
  congr 2

theorem cpull_iff {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull f I n) ↔ Function.Bijective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) ∧
      (Function.Injective (cpull f I n) ↔ Function.Injective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) :=
  conj_iff _ _ (CohomologyClass.homAddEquiv (K := L) (L := I) (n := n)).toEquiv
    (CohomologyClass.homAddEquiv (K := K) (L := I) (n := n)).toEquiv (fun x => by
      simp [toHom_cpull])

theorem main_iff (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (P j : ℤ) :
    (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) ∧
    (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) := by
  let s0 := (CochainComplex.singleFunctor (Shv R) 0).map φ
  let sp := (CochainComplex.singleFunctor (Shv R) (-P)).map φ
  let E := (CochainComplex.singleFunctors (Shv R)).shiftIso P (-P) 0 (by omega)
  obtain ⟨b1, i1⟩ := cpull_iff sp I j
  obtain ⟨b2, i2⟩ := pre_conj ((Qt R).map sp) ((Qt R).map (s0⟦P⟧'))
    ((Qt R).mapIso (E.symm.app A)) ((Qt R).mapIso (E.symm.app B)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact E.inv.naturality φ) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b3, i3⟩ := pre_conj ((Qt R).map (s0⟦P⟧')) (((Qt R).map s0)⟦P⟧')
    (((Qt R).commShiftIso P).app _) (((Qt R).commShiftIso P).app _)
    (((Qt R).commShiftIso P).hom.naturality s0) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b4, i4⟩ := pre_shift ((Qt R).map s0) P ((Qt R).obj (I⟦j⟧))
  obtain ⟨b5, i5⟩ := pre_target ((Qt R).map s0)
    ((((Qt R).commShiftIso (-P)).symm.app (I⟦j⟧)) ≪≫
      (Qt R).mapIso ((shiftFunctorAdd' (Cx R) j (-P) (j - P) (by omega)).symm.app I))
  obtain ⟨b6, i6⟩ := cpull_iff s0 I (j - P)
  exact ⟨b6.trans (b5.symm.trans (b4.symm.trans (b3.trans (b2.trans b1.symm)))),
    i6.trans (i5.symm.trans (i4.symm.trans (i3.trans (i2.trans i1.symm))))⟩

theorem shift_of : LateralTheory.E.CxDescPf.shift := by
  intro R _ I A B φ p j
  obtain ⟨hb, hi⟩ := main_iff I φ (p : ℤ) j
  exact ⟨hb.1, hi.1⟩

end LateralTheory.E.shiftPf
