import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StSiegPull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem pullback_map_left_fst' {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
  simp
  exact pullback.lift_fst _ _ _

def pφ : ((Over.pullback f).obj G).left ⟶ G.left := pullback.fst G.hom f

def pφ₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left :=
  (Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f

theorem pφ₂_fst : pφ₂ f G ≫ (fst G G).left = (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by
  rw [show pφ f G = pullback.fst G.hom f from rfl, pφ₂, Category.assoc, ← pullback_map_left_fst',
    ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_fst]

theorem pφ₂_snd : pφ₂ f G ≫ (snd G G).left = (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by
  rw [show pφ f G = pullback.fst G.hom f from rfl, pφ₂, Category.assoc, ← pullback_map_left_fst',
    ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_snd]

theorem isSquare : IsSquare (pφ f G) (pφ₂ f G) := And.intro (pφ₂_fst f G) (pφ₂_snd f G)

theorem adelic_GL2_ext_of_local_components {R : Scheme.{0}} (a b : R ⟶ (G2 G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) :
    a = b := by
  have hab : a ≫ (G ⊗ G).hom = b ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key : (Over.homMk a : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) = Over.homMk b hab.symm := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa using h1
    · ext
      simpa using h2
  exact congrArg Over.Hom.left key

private theorem unit_left_ext_lemma {Z : Scheme.{0}} (u v : Z ⟶ (𝟙_ (Over S)).left)
    (h : u ≫ (𝟙_ (Over S)).hom = v ≫ (𝟙_ (Over S)).hom) : u = v := by
  have key : (Over.homMk u : Over.mk (u ≫ (𝟙_ (Over S)).hom) ⟶ 𝟙_ (Over S)) = Over.homMk v h.symm :=
    CartesianMonoidalCategory.toUnit_unique _ _
  exact congrArg Over.Hom.left key

theorem one_left_pφ :
    (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ f G ≫ (1 : G ⟶ G).left := by
  have e : (toUnit ((Over.pullback f).obj G)).left ≫ (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over S)).hom f = pullback.snd G.hom f := by
    have h0 := Over.w (toUnit ((Over.pullback f).obj G) ≫ Functor.LaxMonoidal.ε (Over.pullback f))
    rw [Over.comp_left, Category.assoc] at h0
    exact h0
  have hε : (toUnit ((Over.pullback f).obj G)).left ≫ (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.fst (𝟙_ (Over S)).hom f = pullback.fst G.hom f ≫ (toUnit G).left := by
    apply unit_left_ext_lemma
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% e, Over.w, pullback.condition]
  rw [Hom.one_def, Hom.one_def, Functor.obj.η_def]
  simp only [Over.comp_left, Category.assoc]
  rw [show pφ f G = pullback.fst G.hom f from rfl, pullback_map_left_fst', reassoc_of% hε]

private theorem mul_left_pphi_lemma_2 :
    (MonObj.mul : (Over.pullback f).obj G ⊗ (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ₂ f G ≫ (MonObj.mul : G ⊗ G ⟶ G).left := by
  rw [Functor.obj.μ_def, Over.comp_left, Category.assoc, show pφ f G = pullback.fst G.hom f from rfl,
    pullback_map_left_fst', pφ₂, Category.assoc]

theorem isGrpPullback : IsGrpPullback ((Over.pullback f).obj G) G f (pφ f G) := by
  refine ⟨IsPullback.of_hasPullback G.hom f, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hl : (lift x₀ y₀).left = (lift x y).left ≫ pφ₂ f G := by
    apply adelic_GL2_ext_of_local_components
    · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst x₀ y₀)
      have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst x y)
      rw [Over.comp_left] at e1 e2
      rw [e1, Category.assoc, pφ₂_fst, reassoc_of% e2, hx]
    · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd x₀ y₀)
      have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd x y)
      rw [Over.comp_left] at e1 e2
      rw [e1, Category.assoc, pφ₂_snd, reassoc_of% e2, hy]
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc, mul_left_pphi_lemma_2 f G,
    ← Category.assoc, ← hl]

theorem lift_one_id :
    (lift (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G) (𝟙 _)).left ≫ pφ₂ f G =
      pφ f G ≫ (lift (1 : G ⟶ G) (𝟙 G)).left := by
  apply adelic_GL2_ext_of_local_components
  · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G) (𝟙 ((Over.pullback f).obj G)))
    have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (1 : G ⟶ G) (𝟙 G))
    rw [Over.comp_left] at e1 e2
    rw [Category.assoc, pφ₂_fst, reassoc_of% e1, Category.assoc, e2]
    exact one_left_pφ f G
  · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G) (𝟙 ((Over.pullback f).obj G)))
    have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (1 : G ⟶ G) (𝟙 G))
    rw [Over.comp_left] at e1 e2
    rw [Category.assoc, pφ₂_snd, reassoc_of% e1, Category.assoc, e2]
    simp only [Over.id_left, Category.id_comp, Category.comp_id]

theorem lift_id_one :
    (lift (𝟙 _) (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G)).left ≫ pφ₂ f G =
      pφ f G ≫ (lift (𝟙 G) (1 : G ⟶ G)).left := by
  apply adelic_GL2_ext_of_local_components
  · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (𝟙 ((Over.pullback f).obj G)) (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G))
    have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (𝟙 G) (1 : G ⟶ G))
    rw [Over.comp_left] at e1 e2
    rw [Category.assoc, pφ₂_fst, reassoc_of% e1, Category.assoc, e2]
    simp only [Over.id_left, Category.id_comp, Category.comp_id]
  · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (𝟙 ((Over.pullback f).obj G)) (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G))
    have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (𝟙 G) (1 : G ⟶ G))
    rw [Over.comp_left] at e1 e2
    rw [Category.assoc, pφ₂_snd, reassoc_of% e1, Category.assoc, e2]
    exact one_left_pφ f G

theorem lift_swap :
    (lift (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G))
      (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G))).left ≫ pφ₂ f G =
      pφ₂ f G ≫ (lift (snd G G) (fst G G)).left := by
  apply adelic_GL2_ext_of_local_components
  · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)) (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)))
    have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (snd G G) (fst G G))
    rw [Over.comp_left] at e1 e2
    rw [Category.assoc, pφ₂_fst, reassoc_of% e1, Category.assoc, e2]
    rw [pφ₂_snd]
  · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)) (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)))
    have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (snd G G) (fst G G))
    rw [Over.comp_left] at e1 e2
    rw [Category.assoc, pφ₂_snd, reassoc_of% e1, Category.assoc, e2]
    rw [pφ₂_fst]

end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
