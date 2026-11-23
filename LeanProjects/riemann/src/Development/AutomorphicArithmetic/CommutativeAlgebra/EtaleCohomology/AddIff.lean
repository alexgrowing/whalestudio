import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ZeroPull

noncomputable section

open CategoryTheory Opposite

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

private def pre {A : C} (S : Fam A) : Presieve (op A : Cᵒᵖ) :=
  Presieve.ofArrows (fun i => op (S.B i)) (fun i => (S.f i).op)

private def cov (Pa : Parts C) : Coverage Cᵒᵖ where
  coverings X := {R | ∃ S : Fam X.unop, Pa.Cov S ∧ R = pre S}
  pullback := by
    rintro X Y f R ⟨S, hS, rfl⟩
    obtain ⟨B', f', ψ, hc, hcomm⟩ := Pa.pull f.unop S hS
    refine ⟨_, ⟨⟨S.ι, B', f'⟩, hc, rfl⟩, ?_⟩
    rintro Z g ⟨i⟩
    refine ⟨op (S.B i), (ψ i).op, (S.f i).op, Presieve.ofArrows.mk i, ?_⟩
    apply Quiver.Hom.unop_inj
    simpa using hcomm i

private abbrev Jt (Pa : Parts C) : GrothendieckTopology Cᵒᵖ := (cov Pa).toGrothendieck

private theorem add_iff (Pa : Parts C) (F : Coef C) :
    Pa.Add F ↔ Presheaf.IsSheaf (Jt Pa) (unopUnop C ⋙ F) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat.{1}),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
  constructor
  · rintro h X R ⟨S, hS, rfl⟩
    refine (Presieve.isSheafFor_arrows_iff _ _).2 fun x _ => ?_
    obtain ⟨t, ht⟩ := (h _ S hS).2 x
    exact ⟨t, fun i => congrFun ht i,
      fun t' ht' => (h _ S hS).1 (funext fun i => (ht' i).trans (congrFun ht i).symm)⟩
  · intro h A S hS
    have arrows : ∀ {X : C} (S : Fam X), Pa.Cov S → ∀ x : ∀ i, F.obj (S.B i),
        Presieve.Arrows.Compatible ((unopUnop C ⋙ F) ⋙ forget AddCommGrpCat.{1})
          (fun i => (S.f i).op) x → ∃! t, ∀ i, (F.map (S.f i)).hom t = x i :=
      fun {X} S hS x hx =>
        (Presieve.isSheafFor_arrows_iff _ _).1 (h (X := op X) (pre S) ⟨S, hS, rfl⟩) x hx
    have sub : ∀ X : C, Pa.Cov (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam X) →
        Subsingleton (F.obj X) := fun X hX => ⟨fun a b =>
      (arrows _ hX (fun e => e.elim) (fun e => e.elim)).unique (fun e => e.elim) (fun e => e.elim)⟩
    have compat : ∀ x : ∀ i, F.obj (S.B i),
        Presieve.Arrows.Compatible ((unopUnop C ⋙ F) ⋙ forget AddCommGrpCat.{1})
          (fun i => (S.f i).op) x := by
      intro x i j Z gi gj e
      have e' : S.f i ≫ gi.unop = S.f j ≫ gj.unop := congrArg Quiver.Hom.unop e
      by_cases hij : i = j
      · subst hij
        have : gi.unop = gj.unop := (Pa.epi S hS i).left_cancellation _ _ e'
        rw [Quiver.Hom.unop_inj this]
      · have := sub _ (Pa.disj S hS hij gi.unop gj.unop e')
        exact Subsingleton.elim (α := F.obj Z.unop) _ _
    constructor
    · intro a b hab
      exact (arrows S hS _ (compat fun i => (F.map (S.f i)).hom a)).unique (fun i => rfl)
        (fun i => (congrFun hab i).symm)
    · intro x
      obtain ⟨t, ht, -⟩ := arrows S hS x (compat x)
      exact ⟨t, funext ht⟩

private theorem enough (Pa : Parts C) : EnoughInjectives (Sheaf (Jt Pa) AddCommGrpCat.{1}) :=
  haveI : EssentiallySmall.{1} Cᵒᵖ := essentiallySmall_of_small_of_locallySmall _
  haveI : IsGrothendieckAbelian.{1} (Sheaf (Jt Pa) AddCommGrpCat.{1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  inferInstance

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.emb :
    UpperTheory.Ru.crystallineComparison.Emb := by
  intro C _ Pa F hF
  haveI := enough Pa
  let Fs : Sheaf (Jt Pa) AddCommGrpCat.{1} := ⟨unopUnop C ⋙ F, (add_iff Pa F).1 hF⟩
  let I := Injective.under Fs
  let G := (sheafToPresheaf (Jt Pa) AddCommGrpCat.{1}).obj I
  have hG : Presheaf.IsSheaf (Jt Pa) G := I.property
  haveI inj : Injective G :=
    Injective.injective_of_adjoint (sheafificationAdjunction (Jt Pa) AddCommGrpCat.{1}) I
  let m := (sheafToPresheaf (Jt Pa) AddCommGrpCat.{1}).map (Injective.ι Fs)
  have hm : Mono m := inferInstance
  refine ⟨opOp C ⋙ G, { app := fun X => m.app (op (op X)), naturality := fun X Y f => m.naturality f.op.op }, ?_, ?_, ?_⟩
  · rw [NatTrans.mono_iff_mono_app]
    intro X
    exact (NatTrans.mono_iff_mono_app m).1 hm _
  · exact Injective.injective_of_adjoint
      ((opOpEquivalence C).congrLeft (E := AddCommGrpCat.{1})).symm.toAdjunction G
  · exact (add_iff Pa _).2 hG
