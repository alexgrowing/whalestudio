import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PowCart

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}

theorem square_over_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G2 G).left}
    (h : ∀ i, a ≫ (x2 G i).left = b ≫ (x2 G i).left) : a = b :=
  pullback.hom_ext (h 0) (h 1)

theorem isPullback_two (hp : IsPullback β G'.hom G.hom f) :
    IsPullback (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left (G2 G').hom (G2 G).hom f := by
  set F2 := (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left with hF2
  have f2 : ∀ i, F2 ≫ (x2 G i).left = (x2 G' i).left ≫ β := fun i => by
    fin_cases i
    · exact congrArg (fun z => z.left) (lift_fst (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
    · exact congrArg (fun z => z.left) (lift_snd (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
  have w : F2 ≫ (G2 G).hom = (G2 G').hom ≫ f := Over.w (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))
  have ex : ∀ s : PullbackCone (G2 G).hom f, ∃ l : s.pt ⟶ (G2 G').left,
      l ≫ F2 = s.fst ∧ l ≫ (G2 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 2 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x2 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x2 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G2 G' := lift (x 0) (x 1)
    have lx : ∀ i, l ≫ x2 G' i = x i := fun i => by fin_cases i <;> simp [l, x2]
    refine ⟨l.left, square_over_hom_ext _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f2, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => square_over_hom_ext _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f2, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem fourth_power_over_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G4 G).left}
    (h : ∀ i, a ≫ (x4 G i).left = b ≫ (x4 G i).left) : a = b := by
  apply pullback.hom_ext
  · exact h 0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact h 1
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]; exact h 2
      · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]; exact h 3

theorem isPullback_four (hp : IsPullback β G'.hom G.hom f) :
    IsPullback (lift (pushPt hp.w (x4 G' 0)) (lift (pushPt hp.w (x4 G' 1))
      (lift (pushPt hp.w (x4 G' 2)) (pushPt hp.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f := by
  set L4 := lift (pushPt hp.w (x4 G' 0)) (lift (pushPt hp.w (x4 G' 1))
      (lift (pushPt hp.w (x4 G' 2)) (pushPt hp.w (x4 G' 3)))) with hL4
  have f4 : ∀ i, L4.left ≫ (x4 G i).left = (x4 G' i).left ≫ β := fun i => by
    rw [← Over.comp_left]
    have : L4 ≫ x4 G i = pushPt hp.w (x4 G' i) := by fin_cases i <;> simp [L4, x4]
    rw [this]; rfl
  have w : L4.left ≫ (G4 G).hom = (G4 G').hom ≫ f := Over.w L4
  have ex : ∀ s : PullbackCone (G4 G).hom f, ∃ l : s.pt ⟶ (G4 G').left,
      l ≫ L4.left = s.fst ∧ l ≫ (G4 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 4 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x4 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x4 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G4 G' := lift (x 0) (lift (x 1) (lift (x 2) (x 3)))
    have lx : ∀ i, l ≫ x4 G' i = x i := fun i => by fin_cases i <;> simp [l, x4]
    refine ⟨l.left, fourth_power_over_hom_ext _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f4, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => fourth_power_over_hom_ext _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f4, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem isPullback_three [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (gp : IsGrpPullback G' G f β) :
    IsPullback (cubeMapOf gp).F3 (G3 G').hom (G3 G).hom f := by
  have hp := gp.1
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 G' i).left ≫ β := cubeMap_comp_proj_three (cubeMapOf gp)
  have w : (cubeMapOf gp).F3 ≫ (G3 G).hom = (G3 G').hom ≫ f :=
    Over.w (lift (pushPt hp.w (x3 G' 0)) (lift (pushPt hp.w (x3 G' 1)) (pushPt hp.w (x3 G' 2))))
  have ex : ∀ s : PullbackCone (G3 G).hom f, ∃ l : s.pt ⟶ (G3 G').left,
      l ≫ (cubeMapOf gp).F3 = s.fst ∧ l ≫ (G3 G').hom = s.snd := by
    intro s
    let P : Over S' := Over.mk s.snd
    let x : Fin 3 → (P ⟶ G') := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ β = s.fst ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 G' := lift (x 0) (lift (x 1) (x 2))
    have lx : ∀ i, l ≫ x3 G' i = x i := fun i => by fin_cases i <;> simp [l, x3]
    refine ⟨l.left, hom_ext_triple _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f3, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => hom_ext_triple _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f3, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem isPullback_pow {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β) :
    IsPullback (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left (G2 G').hom (G2 G).hom f ∧
    IsPullback (cubeMapOf h).F3 (G3 G').hom (G3 G).hom f ∧
    IsPullback (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
      (pushPt h.1.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f :=
  ⟨isPullback_two h.1, isPullback_three h, isPullback_four h.1⟩

example : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), IsPullback (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left (G2 G').hom (G2 G).hom f ∧ IsPullback (cubeMapOf h).F3 (G3 G').hom (G3 G).hom f ∧ IsPullback (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f :=
  @isPullback_pow

end GlobalTheory.Mum.PowCart
