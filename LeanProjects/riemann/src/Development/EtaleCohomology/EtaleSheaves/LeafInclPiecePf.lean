import Development.EtaleCohomology.EtaleSheaves.LeafInclDescendPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf LateralTheory.E.LeafInclDescendPf

namespace LateralTheory.E.LeafInclPiecePf

theorem incl_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1)
    (h : R ≤ R'') (h1' : R1 ≤ R'') : incl h1' ≫ incl h1 = incl h := by
  simp only [incl]
  rw [← Spec.map_comp]
  rfl

def lvl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R'')
    (h1' : R1 ≤ R'') {D : Scheme.{0}} (q : D ⟶ Sp R) : pullback q (incl h) ⟶ pullback q (incl h1) :=
  pullback.lift (pullback.fst q (incl h)) (pullback.snd q (incl h) ≫ incl h1') (by
    rw [pullback.condition, Category.assoc, incl_comp h1 h h1'])

def descMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R'')
    (h1' : R1 ≤ R'') {DU DW : Scheme.{0}} (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R)
    (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1)) (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1)) :
    pullback qW (incl h) ⟶ pullback qU (incl h) :=
  pullback.lift (lvl h1 h h1' qW ≫ ψ ≫ pullback.fst qU (incl h1)) (pullback.snd qW (incl h)) (by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hψ, lvl, pullback.lift_snd_assoc, Category.assoc, incl_comp h1 h h1'])

theorem bcLift_lvl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1)
    (h : R ≤ R'') (h1' : R1 ≤ R'') {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D}
    (w : v ≫ q = g ≫ toR R) : bcLift h w ≫ lvl h1 h h1' q = bcLift h1 w := by
  apply pullback.hom_ext
  · unfold lvl bcLift
    rw [Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
  · unfold lvl bcLift
    rw [Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc, toR_eq]

def LeafInclMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R)),
    ∃ (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG ∧
      ∃ ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1),
        ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1) ∧
        bcLift h1 hW.w ≫ ψ = X.homOfLE hWU ≫ bcLift h1 hU.w

def LeafInclOpen : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R))
    (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG →
    ∀ (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1))
      (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1)),
      bcLift h1 hW.w ≫ ψ = X.homOfLE hWU ≫ bcLift h1 hU.w →
    ∃ R' : Subalgebra k Ω, R1 ≤ R' ∧ R'.FG ∧ ∀ (R'' : Subalgebra k Ω) (h : R ≤ R'') (h1' : R1 ≤ R''), R' ≤ R'' →
      IsOpenImmersion (descMap h1 h h1' qU qW ψ hψ)

theorem LeafInclPiece_of (hA : LeafInclMap) (hB : LeafInclOpen) : LeafInclPiece := by
  intro k _ Ω _ _ X f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R1, h1, hR1, ψ, hψ, hc⟩ := hA k Ω f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R', h1R', hR', H⟩ := hB k Ω f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW R1 h1 hR1 ψ hψ hc
  refine ⟨R', h1.trans h1R', hR', fun R'' h hR'' => ?_⟩
  have h1' : R1 ≤ R'' := h1R'.trans hR''
  refine ⟨descMap h1 h h1' qU qW ψ hψ, H R'' h h1' hR'', pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · simp only [descMap, Category.assoc, pullback.lift_fst]
    rw [reassoc_of% (bcLift_lvl h1 h h1' hW.w), reassoc_of% hc]
    unfold bcLift
    erw [pullback.lift_fst, pullback.lift_fst]
  · simp only [descMap, Category.assoc, pullback.lift_snd]
    unfold bcLift
    erw [pullback.lift_snd, pullback.lift_snd]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc]

end LateralTheory.E.LeafInclPiecePf
end
