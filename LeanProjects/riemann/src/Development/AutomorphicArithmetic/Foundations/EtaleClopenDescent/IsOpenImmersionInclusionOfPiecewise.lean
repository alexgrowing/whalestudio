import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafInclPiecePf
import Development.AutomorphicArithmetic.CommutativeAlgebra.LimitOfCofilteredAffineBaseChangeSquares
import Development.AutomorphicArithmetic.CommutativeAlgebra.LimitCompactOfCofilteredCartesianAffineTransitio

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf LateralTheory.E.LeafInclDescendPf LateralTheory.E.LeafInclPiecePf

namespace UpperTheory.Cb.StagedBaseChange

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

abbrev Idx (R1 : Subalgebra k Ω) : Type := {S : Subalgebra k Ω // R1 ≤ S ∧ S.FG}

theorem idx_directed (R1 : Subalgebra k Ω) : IsDirected (Idx R1) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, a.2.1.trans le_sup_left, a.2.2.sup b.2.2⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

def ringF (R1 : Subalgebra k Ω) : Idx R1 ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of S.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom

def ringC (R1 : Subalgebra k Ω) : Cocone (ringF R1) where
  pt := CommRingCat.of Ω
  ι := { app := fun S => CommRingCat.ofHom (algebraMap S.1 Ω) }

theorem ringC_isColimit (R1 : Subalgebra k Ω) (hR1 : R1.FG) : Nonempty (IsColimit (ringC R1)) := by
  haveI := idx_directed R1
  haveI : Nonempty (Idx R1) := ⟨⟨R1, le_rfl, hR1⟩⟩
  haveI : IsFiltered (Idx R1) := inferInstance
  haveI : ReflectsColimitsOfShape (Idx R1) (forget CommRingCat) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    let S : Idx R1 := ⟨R1 ⊔ Algebra.adjoin k {x}, le_sup_left,
      hR1.sup (Subalgebra.fg_def.2 ⟨{x}, Set.finite_singleton x, rfl⟩)⟩
    have hx : x ∈ S.1 := (le_sup_right : _ ≤ R1 ⊔ Algebra.adjoin k {x}) (Algebra.subset_adjoin rfl)
    exact ⟨S, ⟨x, hx⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, i.2.1.trans le_sup_left, i.2.2.sup j.2.2⟩, homOfLE (le_sup_left (a := i.1)),
      homOfLE (le_sup_right (b := j.1)), ?_⟩
    apply Subtype.ext
    exact h

def baseD (R1 : Subalgebra k Ω) : (Idx R1)ᵒᵖ ⥤ Scheme.{0} := (ringF R1).op ⋙ Scheme.Spec

def baseC (R1 : Subalgebra k Ω) : Cone (baseD R1) := Scheme.Spec.mapCone (ringC R1).op

theorem baseC_isLimit (R1 : Subalgebra k Ω) (hR1 : R1.FG) : Nonempty (IsLimit (baseC R1)) := by
  obtain ⟨hc⟩ := ringC_isColimit R1 hR1
  exact ⟨isLimitOfPreserves Scheme.Spec hc.op⟩

instance (R1 : Subalgebra k Ω) {i j : (Idx R1)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((baseD R1).map f) := by
  show IsAffineHom (Spec.map _)
  infer_instance

theorem lvl_fst {A B D0 : Subalgebra k Ω} (hA : D0 ≤ A) (hB : D0 ≤ B) (hAB : A ≤ B)
    {D : Scheme.{0}} (q : D ⟶ Sp D0) :
    lvl hA hB hAB q ≫ pullback.fst q (incl hA) = pullback.fst q (incl hB) :=
  pullback.lift_fst _ _ _

theorem lvl_snd {A B D0 : Subalgebra k Ω} (hA : D0 ≤ A) (hB : D0 ≤ B) (hAB : A ≤ B)
    {D : Scheme.{0}} (q : D ⟶ Sp D0) :
    lvl hA hB hAB q ≫ pullback.snd q (incl hA) = pullback.snd q (incl hB) ≫ incl hAB :=
  pullback.lift_snd _ _ _

theorem lvl_comp {A B C D0 : Subalgebra k Ω} (hA : D0 ≤ A) (hB : D0 ≤ B) (hC : D0 ≤ C) (hAB : A ≤ B) (hBC : B ≤ C)
    {D : Scheme.{0}} (q : D ⟶ Sp D0) :
    lvl hB hC hBC q ≫ lvl hA hB hAB q = lvl hA hC (hAB.trans hBC) q := by
  apply pullback.hom_ext
  · rw [Category.assoc, lvl_fst, lvl_fst, lvl_fst]
  · rw [Category.assoc, lvl_snd, reassoc_of% (lvl_snd hB hC hBC q), lvl_snd, incl_comp hAB (hAB.trans hBC) hBC]

theorem lvl_self {A D0 : Subalgebra k Ω} (hA : D0 ≤ A) {D : Scheme.{0}} (q : D ⟶ Sp D0) :
    lvl hA hA le_rfl q = 𝟙 _ := by
  have h : incl (le_refl A) = 𝟙 (Sp A) := by
    rw [incl, show CommRingCat.ofHom (Subalgebra.inclusion (le_refl A)).toRingHom = 𝟙 _ from by ext; rfl]
    exact Scheme.Spec.map_id _
  apply pullback.hom_ext
  · rw [lvl_fst, Category.id_comp]
  · rw [lvl_snd, h, Category.comp_id, Category.id_comp]

theorem lvl_isPullback {A B D0 : Subalgebra k Ω} (hA : D0 ≤ A) (hB : D0 ≤ B) (hAB : A ≤ B)
    {D : Scheme.{0}} (q : D ⟶ Sp D0) :
    IsPullback (lvl hA hB hAB q) (pullback.snd q (incl hB)) (pullback.snd q (incl hA)) (incl hAB) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl hA)) (v₁₃ := q) (h₂₂ := incl hA) ?_
    (lvl_snd hA hB hAB q) (IsPullback.of_hasPullback q (incl hA))
  rw [lvl_fst, incl_comp hA hB hAB]
  exact IsPullback.of_hasPullback q (incl hB)

def stageD {R R1 : Subalgebra k Ω} (h1 : R ≤ R1) {D : Scheme.{0}} (q : D ⟶ Sp R) : (Idx R1)ᵒᵖ ⥤ Scheme.{0} where
  obj S := pullback q (incl (h1.trans S.unop.2.1))
  map {S T} f := lvl (h1.trans T.unop.2.1) (h1.trans S.unop.2.1) (leOfHom f.unop) q
  map_id S := lvl_self _ q
  map_comp {S T V} f g := (lvl_comp _ _ _ (leOfHom g.unop) (leOfHom f.unop) q).symm

def stageP {R R1 : Subalgebra k Ω} (h1 : R ≤ R1) {D : Scheme.{0}} (q : D ⟶ Sp R) : stageD h1 q ⟶ baseD R1 where
  app S := pullback.snd q (incl (h1.trans S.unop.2.1))
  naturality {S T} f := lvl_snd (h1.trans T.unop.2.1) (h1.trans S.unop.2.1) (leOfHom f.unop) q

def stageC {R R1 : Subalgebra k Ω} (h1 : R ≤ R1) {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D}
    (w : v ≫ q = g ≫ toR R) : Cone (stageD h1 q) where
  pt := Y
  π := { app := fun S => bcLift (h1.trans S.unop.2.1) w
         naturality := fun S T f => (Category.id_comp _).trans
          (bcLift_lvl (h1.trans T.unop.2.1) (h1.trans S.unop.2.1) (leOfHom f.unop) w).symm }

theorem stageC_isLimit {R R1 : Subalgebra k Ω} (h1 : R ≤ R1) (hR1 : R1.FG) {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω}
    {q : D ⟶ Sp R} {v : Y ⟶ D} (hp : IsPullback v g q (toR R)) : Nonempty (IsLimit (stageC h1 hp.w)) := by
  haveI := idx_directed R1
  haveI : Nonempty (Idx R1) := ⟨⟨R1, le_rfl, hR1⟩⟩
  haveI : IsFiltered (Idx R1) := inferInstance
  haveI : IsCofiltered (Idx R1)ᵒᵖ := inferInstance
  haveI : IsConnected (Idx R1)ᵒᵖ := IsCofiltered.isConnected _
  obtain ⟨hc⟩ := baseC_isLimit R1 hR1
  refine ⟨isLimitOfIsPullbackOfIsConnected (stageP h1 q) _ (baseC R1) ⟨g, ?_⟩ ?_ hc⟩
  · intro S
    exact (pullback.lift_snd _ _ _).symm
  · intro S
    exact bcLift_isPullback _ hp

section
variable {R R1 : Subalgebra k Ω} (h1 : R ≤ R1) {DU DW : Scheme.{0}} (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R)
  (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1))
  (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1))

include h1 in
theorem descMap_fst {A : Subalgebra k Ω} (hA : R ≤ A) (h1A : R1 ≤ A) :
    descMap h1 hA h1A qU qW ψ hψ ≫ pullback.fst qU (incl hA) =
      lvl h1 hA h1A qW ≫ ψ ≫ pullback.fst qU (incl h1) :=
  pullback.lift_fst _ _ _

theorem descMap_snd {A : Subalgebra k Ω} (hA : R ≤ A) (h1A : R1 ≤ A) :
    descMap h1 hA h1A qU qW ψ hψ ≫ pullback.snd qU (incl hA) = pullback.snd qW (incl hA) :=
  pullback.lift_snd _ _ _

theorem descMap_lvl {A B : Subalgebra k Ω} (hA : R ≤ A) (hB : R ≤ B) (h1A : R1 ≤ A) (h1B : R1 ≤ B) (hAB : A ≤ B) :
    lvl hA hB hAB qW ≫ descMap h1 hA h1A qU qW ψ hψ = descMap h1 hB h1B qU qW ψ hψ ≫ lvl hA hB hAB qU := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, lvl_fst, descMap_fst, descMap_fst,
      reassoc_of% (lvl_comp h1 hA hB h1A hAB qW)]
  · rw [Category.assoc, Category.assoc, lvl_snd, descMap_snd, reassoc_of% (descMap_snd h1 qU qW ψ hψ hB h1B), lvl_snd]

theorem descMap_isPullback {A B : Subalgebra k Ω} (hA : R ≤ A) (hB : R ≤ B) (h1A : R1 ≤ A) (h1B : R1 ≤ B)
    (hAB : A ≤ B) :
    IsPullback (lvl hA hB hAB qW) (descMap h1 hB h1B qU qW ψ hψ) (descMap h1 hA h1A qU qW ψ hψ)
      (lvl hA hB hAB qU) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd qU (incl hB)) (v₂₂ := pullback.snd qU (incl hA)) (h₃₁ := incl hAB)
    ?_ (descMap_lvl h1 qU qW ψ hψ hA hB h1A h1B hAB) (lvl_isPullback hA hB hAB qU)
  rw [descMap_snd, descMap_snd]
  exact lvl_isPullback hA hB hAB qW

def stageA : stageD h1 qW ⟶ stageD h1 qU where
  app S := descMap h1 (h1.trans S.unop.2.1) S.unop.2.1 qU qW ψ hψ
  naturality {S T} f := descMap_lvl h1 qU qW ψ hψ (h1.trans T.unop.2.1) (h1.trans S.unop.2.1) T.unop.2.1 S.unop.2.1
    (leOfHom f.unop) |>.symm ▸ rfl

theorem stageA_comp : stageA h1 qU qW ψ hψ ≫ stageP h1 qU = stageP h1 qW := by
  ext S : 2
  exact descMap_snd h1 qU qW ψ hψ _ _

end

theorem bcLift_fst {R A : Subalgebra k Ω} (h : R ≤ A) {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D}
    (w : v ≫ q = g ≫ toR R) : bcLift h w ≫ pullback.fst q (incl h) = v :=
  pullback.lift_fst _ _ _

theorem bcLift_snd {R A : Subalgebra k Ω} (h : R ≤ A) {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D}
    (w : v ≫ q = g ≫ toR R) : bcLift h w ≫ pullback.snd q (incl h) = g ≫ toR A :=
  pullback.lift_snd _ _ _

theorem fp_stage {E : Scheme.{0}} {A : Type} [CommRing A] (p : E ⟶ Sp A) (hp : FP p) :
    CompactSpace E ∧ QuasiSeparatedSpace E := by
  obtain ⟨-, h2, h3⟩ := hp
  exact ⟨QuasiCompact.compactSpace_of_compactSpace p, quasiSeparatedSpace_of_quasiSeparated p⟩

end UpperTheory.Cb.StagedBaseChange

open UpperTheory.Cb.StagedBaseChange in
theorem UpperTheory.Cb.isOpenImmersion_inclusion_of_piecewise : LateralTheory.E.LeafInclPiecePf.LeafInclOpen := by
  intro k _ Ω _ _ X f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW R1 h1 hR1 ψ hψ hc
  haveI := idx_directed R1
  haveI : Nonempty (Idx R1) := ⟨⟨R1, le_rfl, hR1⟩⟩
  haveI : IsFiltered (Idx R1) := inferInstance
  haveI : IsCofiltered (Idx R1)ᵒᵖ := inferInstance
  let i0 : (Idx R1)ᵒᵖ := op ⟨R1, le_rfl, hR1⟩
  obtain ⟨hcZ⟩ := stageC_isLimit h1 hR1 hW
  obtain ⟨hcY⟩ := stageC_isLimit h1 hR1 hU
  have hZ : ∀ {i j : (Idx R1)ᵒᵖ} (e : i ⟶ j), IsPullback ((stageD h1 qW).map e) ((stageP h1 qW).app i)
      ((stageP h1 qW).app j) ((baseD R1).map e) := fun {i j} e =>
    lvl_isPullback (h1.trans j.unop.2.1) (h1.trans i.unop.2.1) (leOfHom e.unop) qW
  have hY : ∀ {i j : (Idx R1)ᵒᵖ} (e : i ⟶ j), IsPullback ((stageD h1 qU).map e) ((stageP h1 qU).app i)
      ((stageP h1 qU).app j) ((baseD R1).map e) := fun {i j} e =>
    lvl_isPullback (h1.trans j.unop.2.1) (h1.trans i.unop.2.1) (leOfHom e.unop) qU
  have sZ : ∀ i : (Idx R1)ᵒᵖ, FP ((stageP h1 qW).app i) := fun i => fp_snd _ _ hqW
  have sY : ∀ i : (Idx R1)ᵒᵖ, FP ((stageP h1 qU).app i) := fun i => fp_snd _ _ hqU
  have cZ := fun i => (fp_stage _ (sZ i)).1
  have qZ := fun i => (fp_stage _ (sZ i)).2
  have cY := fun i => (fp_stage _ (sY i)).1
  have qY := fun i => (fp_stage _ (sY i)).2
  have hm : ∀ i, (stageC h1 hW.w).π.app i ≫ (stageA h1 qU qW ψ hψ).app i =
      X.homOfLE hWU ≫ (stageC h1 hU.w).π.app i := by
    intro i
    change bcLift _ hW.w ≫ descMap h1 _ i.unop.2.1 qU qW ψ hψ = X.homOfLE hWU ≫ bcLift _ hU.w
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, descMap_fst, bcLift_fst,
        reassoc_of% (bcLift_lvl h1 (h1.trans i.unop.2.1) i.unop.2.1 hW.w), reassoc_of% hc, bcLift_fst]
    · rw [Category.assoc, Category.assoc, descMap_snd, bcLift_snd, bcLift_snd]
      simp only [Category.assoc, Scheme.homOfLE_ι_assoc]
  haveI : IsOpenImmersion (X.homOfLE hWU) := by
    haveI : IsOpenImmersion (X.homOfLE hWU ≫ U.ι) := by
      rw [Scheme.homOfLE_ι]
      infer_instance
    exact IsOpenImmersion.of_comp _ U.ι
  let m : (stageC h1 hW.w).pt ⟶ (stageC h1 hU.w).pt := X.homOfLE hWU
  haveI hmo : IsOpenImmersion m := ‹IsOpenImmersion (X.homOfLE hWU)›
  obtain ⟨j, e, V, hV, hα, hπ⟩ := UpperTheory.limit_of_cofiltered_affine_base_change_squares _ (baseD R1) (stageD h1 qW) (stageD h1 qU) (stageA h1 qU qW ψ hψ)
    (stageP h1 qW) (stageP h1 qU) (stageA_comp h1 qU qW ψ hψ) hZ hY _ hcZ _ hcY cZ qZ cY qY i0 m hm
  obtain ⟨l, e2, hl⟩ := UpperTheory.limit_compact_of_cofiltered_cartesian_affine_transition _ (baseD R1) (stageD h1 qW) (stageD h1 qU) (stageA h1 qU qW ψ hψ)
    (stageP h1 qW) (stageP h1 qU) (stageA_comp h1 qU qW ψ hψ) hZ hY _ hcZ _ hcY cZ qZ cY qY i0 (sZ i0).1
    (by haveI := (sY i0).1; infer_instance) m hm j e V hV hα hπ
  refine ⟨l.unop.1, l.unop.2.1, l.unop.2.2, fun R'' h h1' hle => ?_⟩
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (descMap_isPullback h1 qU qW ψ hψ (h1.trans l.unop.2.1) h l.unop.2.1 h1' hle) hl

end
