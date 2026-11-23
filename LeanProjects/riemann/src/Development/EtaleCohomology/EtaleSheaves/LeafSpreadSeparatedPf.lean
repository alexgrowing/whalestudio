import Development.EtaleCohomology.EtaleSheaves.LeafSpreadProperPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafSpreadSeparatedPf

theorem incl_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h : R ≤ S)
    (h' : S ≤ R') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]; rfl

theorem sep_of_stage {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h : R ≤ S)
    (hS : S ≤ R') (hR : R ≤ R') {D E : Scheme.{0}} (q : D ⟶ Sp R) [IsSeparated (pullback.snd q (incl h))]
    (q' : E ⟶ Sp R') (r : E ⟶ D) (hE : IsPullback r q' q (incl hR)) : IsSeparated q' := by
  have hc : r ≫ q = (q' ≫ incl hS) ≫ incl h := by
    rw [Category.assoc, incl_comp]; exact hE.w
  have outer : IsPullback (pullback.lift r (q' ≫ incl hS) hc ≫ pullback.fst q (incl h)) q' q
      (incl hS ≫ incl h) := by
    rw [pullback.lift_fst, incl_comp]; exact hE
  have sq := IsPullback.of_right outer (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h))
  exact MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance

def BC {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p) (t : T ⟶ Z) :
    pullback p t ⟶ pullback g t :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp [w]) (by simp)

def LeafClosedImmSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp R),
    (LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g) →
    (LocallyOfFinitePresentation (f ≫ g) ∧ QuasiCompact (f ≫ g) ∧ QuasiSeparated (f ≫ g)) →
    IsClosedImmersion (BC f g (f ≫ g) rfl (toR R)) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ IsClosedImmersion (BC f g (f ≫ g) rfl (incl h))

def LeafDiagBC : Prop := ∀ {D Z T : Scheme.{0}} (q : D ⟶ Z) (t : T ⟶ Z),
    IsSeparated (pullback.snd q t) ↔ IsClosedImmersion (BC (pullback.diagonal q) (pullback.snd q q ≫ q) q (by simp) t)

theorem ci_congr {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p) (t : T ⟶ Z) :
    IsClosedImmersion (BC f g p w t) ↔ IsClosedImmersion (BC f g (f ≫ g) rfl t) := by
  subst w; rfl

theorem separated_base_change_iff_diagonal_closed_immersion_holds : LeafDiagBC := by
  intro D Z T q t
  have e1 : pullback.snd q t = (pullbackSymmetry q t).hom ≫ pullback.fst t q := by simp
  have e2 : IsSeparated (pullback.snd q t) ↔ IsSeparated (pullback.fst t q) := by
    rw [e1]; exact MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated) _ _
  rw [e2]
  have e3 : IsSeparated (pullback.fst t q) ↔ IsClosedImmersion (pullback.diagonal (pullback.fst t q)) :=
    ⟨fun h => h.isClosedImmersion_diagonal, fun h => ⟨h⟩⟩
  rw [e3, diagonal_pullback_fst, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  have : ((Over.pullback t).map (Over.homMk (pullback.diagonal q) : Over.mk q ⟶ Over.mk (pullback.snd q q ≫ q))).left
      = BC (pullback.diagonal q) (pullback.snd q q ≫ q) q (by simp) t := by
    apply pullback.hom_ext <;> simp only [BC, pullback.map, Category.comp_id] <;> rfl
  rw [this]

theorem of_two (hC : LeafClosedImmSpread) (hD : LeafDiagBC) :
    LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated := by
  intro k _ Ω _ _ R hR C D c q v hf hc hv
  obtain ⟨h1, h2, h3⟩ := hf
  have s0 : IsSeparated (pullback.snd q (toR R)) := by
    rw [← hv.isoPullback_inv_snd]; infer_instance
  have ci := (ci_congr _ _ _ _ _).1 ((hD q (toR R)).1 s0)
  have hfg : pullback.diagonal q ≫ pullback.snd q q ≫ q = q := by simp
  obtain ⟨S, h, hS, ci'⟩ := hC k Ω R hR (pullback.diagonal q) (pullback.snd q q ≫ q)
    ⟨inferInstance, inferInstance, inferInstance⟩ (by rw [hfg]; exact ⟨h1, h2, h3⟩) ci
  have := (hD q (incl h)).2 ((ci_congr _ _ _ (by simp) _).2 ci')
  exact ⟨S, h, hS, fun R' hS' hRR E q' r hE => sep_of_stage h hS' hRR q q' r hE⟩

end LateralTheory.E.LeafSpreadSeparatedPf

end
