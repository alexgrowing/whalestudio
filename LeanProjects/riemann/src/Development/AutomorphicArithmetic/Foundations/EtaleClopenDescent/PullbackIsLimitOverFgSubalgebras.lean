import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafInclPiecePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf LateralTheory.E.LeafInclDescendPf
  LateralTheory.E.LeafInclPiecePf

namespace UpperTheory.Cb.PiLocalization₂

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)

private abbrev Lev : Type := {S : Subalgebra k Ω // R ≤ S ∧ S.FG}

private theorem lev_directed : IsDirected (Lev R) (· ≤ ·) :=
  ⟨fun a b ↦ ⟨⟨a.1 ⊔ b.1, a.2.1.trans le_sup_left, a.2.2.sup b.2.2⟩,
    (le_sup_left : a.1 ≤ a.1 ⊔ b.1), (le_sup_right : b.1 ≤ a.1 ⊔ b.1)⟩⟩

private def rings : Lev R ⥤ CommRingCat.{0} where
  obj s := .of s.1
  map {s t} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h : s.1 ≤ t.1)).toRingHom

private def ringsCocone : Cocone (rings R) where
  pt := .of Ω
  ι := { app s := CommRingCat.ofHom (algebraMap s.1 Ω) }

private def ringsIsColimit (hR : R.FG) : IsColimit (ringsCocone R) := by
  classical
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  refine isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun s a b hab ↦ ?_))
  · let x' : Ω := x
    have hx : (Algebra.adjoin k {x'}).FG := ⟨{x'}, by simp⟩
    refine ⟨⟨R ⊔ Algebra.adjoin k {x'}, le_sup_left, hR.sup hx⟩,
      (⟨x', (le_sup_right : Algebra.adjoin k {x'} ≤ R ⊔ Algebra.adjoin k {x'})
        (Algebra.subset_adjoin rfl)⟩ : (R ⊔ Algebra.adjoin k {x'} : Subalgebra k Ω)), rfl⟩
  · exact ⟨s, 𝟙 s, congrArg _ (Subtype.ext hab)⟩

variable {R} in
private theorem lvl_fst {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) : lvl h1 h h' q ≫ pullback.fst q (incl h1) = pullback.fst q (incl h) :=
  pullback.lift_fst _ _ _

variable {R} in
private theorem lvl_snd {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) :
    lvl h1 h h' q ≫ pullback.snd q (incl h1) = pullback.snd q (incl h) ≫ incl h' :=
  pullback.lift_snd _ _ _

variable {R} in
private theorem lvl_isPullback {R1 R2 : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R2) (h' : R1 ≤ R2)
    {D : Scheme.{0}} (q : D ⟶ Sp R) :
    IsPullback (lvl h1 h h' q) (pullback.snd q (incl h)) (pullback.snd q (incl h1)) (incl h') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h1)) (v₁₃ := q) (h₂₂ := incl h1) ?_
    (lvl_snd h1 h h' q) (IsPullback.of_hasPullback q (incl h1))
  rw [lvl_fst, incl_comp h1 h h']
  exact IsPullback.of_hasPullback q (incl h)

variable {D : Scheme.{0}} (q : D ⟶ Sp R)

private def stages : (Lev R)ᵒᵖ ⥤ Scheme.{0} where
  obj s := pullback q (incl s.unop.2.1)
  map {s t} h := lvl t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q
  map_id s := by
    apply pullback.hom_ext
    · rw [lvl_fst, Category.id_comp]
    · rw [lvl_snd, Category.id_comp]
      exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
  map_comp {s t u} f g := by
    apply pullback.hom_ext
    · rw [lvl_fst, Category.assoc, lvl_fst, lvl_fst]
    · rw [lvl_snd, Category.assoc, lvl_snd, ← Category.assoc, lvl_snd, Category.assoc,
        incl_comp (leOfHom g.unop : u.unop.1 ≤ t.unop.1) (leOfHom (f ≫ g).unop : u.unop.1 ≤ s.unop.1)
          (leOfHom f.unop : t.unop.1 ≤ s.unop.1)]

private def toBase : stages R q ⟶ (rings R).op ⋙ Scheme.Spec where
  app s := pullback.snd q (incl s.unop.2.1)
  naturality s t h := lvl_snd t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q

variable {R q} in

private def stagesCone {Y : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D} (w : v ≫ q = g ≫ toR R) :
    Cone (stages R q) where
  pt := Y
  π :=
    { app s := bcLift s.unop.2.1 w
      naturality s t h := (Category.id_comp _).trans
        (bcLift_lvl t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) w).symm }

variable {R q} in

private def stagesIsLimit (hR : R.FG) {Y : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D}
    (hp : IsPullback v g q (toR R)) : IsLimit (stagesCone hp.w) := by
  classical
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  have : IsFiltered (Lev R) := isFiltered_of_directed_le_nonempty _
  have : IsConnected (Lev R)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfIsPullbackOfIsConnected (toBase R q) (stagesCone hp.w)
    (Scheme.Spec.mapCone (ringsCocone R).op)
    { hom := g
      w s := (pullback.lift_snd _ _ _).symm }
    (fun s ↦ bcLift_isPullback s.unop.2.1 hp)
    (isLimitOfPreserves Scheme.Spec (ringsIsColimit R hR).op)

private def stagesToConstantSpec : stages R q ⟶ (Functor.const _).obj (Sp R) where
  app s := pullback.fst q (incl s.unop.2.1) ≫ q
  naturality s t h := by
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact (lvl_fst t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q) =≫ q |>.trans rfl |> fun e ↦ by
      simpa [stages] using e

variable {R q} in

private theorem factor (hR : R.FG) (hq : FP q) {Y Z : Scheme.{0}} {g : Y ⟶ Sp Ω} {v : Y ⟶ D}
    (hp : IsPullback v g q (toR R)) (qZ : Z ⟶ Sp R) (hZ : LocallyOfFinitePresentation qZ)
    (a : Y ⟶ Z) (ha : a ≫ qZ = v ≫ q) :
    ∃ (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG ∧ ∃ u : pullback q (incl h1) ⟶ Z,
      bcLift h1 hp.w ≫ u = a ∧ u ≫ qZ = pullback.fst q (incl h1) ≫ q := by
  classical
  have : Nonempty (Lev R) := ⟨⟨R, le_rfl, hR⟩⟩
  have := lev_directed R
  have : IsFiltered (Lev R) := isFiltered_of_directed_le_nonempty _
  have i1 : ∀ {s t : (Lev R)ᵒᵖ} (h : s ⟶ t), IsAffineHom ((stages R q).map h) := fun {s t} h ↦
    MorphismProperty.of_isPullback
      (lvl_isPullback t.unop.2.1 s.unop.2.1 (leOfHom h.unop : t.unop.1 ≤ s.unop.1) q).flip inferInstance
  have i2 : ∀ s : (Lev R)ᵒᵖ, CompactSpace ((stages R q).obj s) := fun s ↦ by
    have h : QuasiCompact (pullback.snd q (incl s.unop.2.1)) := (fp_snd q (incl s.unop.2.1) hq).2.1
    change CompactSpace ↥(pullback q (incl s.unop.2.1))
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd q (incl s.unop.2.1))
  have i3 : ∀ s : (Lev R)ᵒᵖ, QuasiSeparatedSpace ((stages R q).obj s) := fun s ↦
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd q (incl s.unop.2.1))).mp
      (fp_snd q (incl s.unop.2.1) hq).2.2
  obtain ⟨s, u, h₁, h₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (stages R q) (stagesToConstantSpec R q) qZ (stagesCone hp.w) (stagesIsLimit hR hp) a (by
      refine NatTrans.ext (funext fun s ↦ ?_)
      change bcLift s.unop.2.1 hp.w ≫ pullback.fst q (incl s.unop.2.1) ≫ q = a ≫ qZ
      rw [ha]
      exact pullback.lift_fst_assoc _ _ _ _)
  exact ⟨s.unop.1, s.unop.2.1, s.unop.2.2, u, h₁, h₂⟩

end UpperTheory.Cb.PiLocalization₂

theorem UpperTheory.Cb.pullback_isLimit_over_fg_subalgebras :
    LateralTheory.E.LeafInclPiecePf.LeafInclMap := by
  intro k _ Ω _ _ X f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R1, h1, hR1, u, hu, hu'⟩ := UpperTheory.Cb.PiLocalization₂.factor hR hqW hW qU hqU.1 (X.homOfLE hWU ≫ vU) (by
    rw [Category.assoc, hU.w, hW.w]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc])
  refine ⟨R1, h1, hR1, pullback.lift u (pullback.snd qW (incl h1)) ?_, pullback.lift_snd _ _ _, ?_⟩
  · rw [hu', pullback.condition]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hu, Category.assoc]
      unfold bcLift
      rw [pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc]
      unfold bcLift
      rw [pullback.lift_snd, pullback.lift_snd]
      simp only [Category.assoc, Scheme.homOfLE_ι_assoc]

end
