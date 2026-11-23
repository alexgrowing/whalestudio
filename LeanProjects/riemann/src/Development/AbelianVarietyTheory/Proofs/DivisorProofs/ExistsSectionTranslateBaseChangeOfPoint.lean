import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.TransBaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]

theorem pullback_map_left_fst {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem mul_left_fst {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    (u * v).left ≫ pullback.fst G.hom f =
      ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
        (μ[G]).left := by
  rw [Hom.mul_def, Functor.obj.μ_def]
  simp only [Over.comp_left, Category.assoc]
  rw [pullback_map_left_fst]

theorem lift_μ_fst {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
      (fst G G).left = u.left ≫ pullback.fst G.hom f := by
  rw [Category.assoc, ← pullback_map_left_fst, ← Category.assoc, ← Over.comp_left, Category.assoc,
    Functor.Monoidal.μ_fst, lift_fst]

theorem lift_μ_snd {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
      (snd G G).left = v.left ≫ pullback.fst G.hom f := by
  rw [Category.assoc, ← pullback_map_left_fst, ← Category.assoc, ← Over.comp_left, Category.assoc,
    Functor.Monoidal.μ_snd, lift_snd]

theorem inv_left_fst {X : Over S'} (u : X ⟶ (Over.pullback f).obj G) :
    (u⁻¹).left ≫ pullback.fst G.hom f = u.left ≫ pullback.fst G.hom f ≫ (ι[G]).left := by
  rw [Hom.inv_def, Functor.obj.ι_def, Over.comp_left, Category.assoc, pullback_map_left_fst]

theorem toUnit_left (X : Over S') : (toUnit X).left = X.hom := Over.w (toUnit X)

theorem ext_tensor {Y : Scheme.{0}} (x y : Y ⟶ (G ⊗ G).left)
    (h1 : x ≫ (fst G G).left = y ≫ (fst G G).left) (h2 : x ≫ (snd G G).left = y ≫ (snd G G).left) :
    x = y :=
  Over.tensorObj_ext _ _ h1 h2

theorem exists_section_translate : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R') (G : Over (Sp R)) [GrpObj G] (c : Sp R' ⟶ G.left), c ≫ G.hom = spMap ρ → ∃ (a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G) (Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left), IsPullback Φ (pullback.snd G.hom (spMap ρ)) (snd G G).left c ∧ Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * snd G G).left ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * (snd G G)⁻¹).left := by
  intro R R' _ _ ρ G _ c hc
  have hw : c ≫ G.hom = 𝟙 (Sp R') ≫ spMap ρ := by simpa using hc
  let a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G :=
    Over.homMk (pullback.lift c (𝟙 _) hw) (by dsimp; rw [pullback.lift_snd])
  have ha : a.left ≫ pullback.fst G.hom (spMap ρ) = c := pullback.lift_fst _ _ _
  have hcond : pullback.fst G.hom (spMap ρ) ≫ G.hom = (pullback.snd G.hom (spMap ρ) ≫ c) ≫ G.hom := by
    rw [Category.assoc, hc, pullback.condition]
  let Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left :=
    (pullback.lift (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ) ≫ c) hcond :
      _ ⟶ pullback G.hom G.hom)
  have hΦ1 : Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) := pullback.lift_fst _ _ _
  have hΦ2 : Φ ≫ (snd G G).left = pullback.snd G.hom (spMap ρ) ≫ c := pullback.lift_snd _ _ _
  have hu : ((toUnit ((Over.pullback (spMap ρ)).obj G)).left) = pullback.snd G.hom (spMap ρ) :=
    toUnit_left _
  refine ⟨a, Φ, ?_, hΦ1, ?_, ?_⟩
  · have outer : IsPullback (Φ ≫ (fst G G).left) (pullback.snd G.hom (spMap ρ)) G.hom (c ≫ G.hom) := by
      rw [hΦ1, hc]; exact IsPullback.of_hasPullback _ _
    have right : IsPullback (fst G G).left (snd G G).left G.hom G.hom :=
      IsPullback.of_hasPullback G.hom G.hom
    exact IsPullback.of_right outer hΦ2 right
  · rw [mul_left_fst, Hom.mul_def, lift_fst_snd, Category.id_comp]
    congr 1
    apply ext_tensor
    · rw [lift_μ_fst, hΦ1, Over.id_left, Category.id_comp]
    · rw [lift_μ_snd, hΦ2, Over.comp_left, Category.assoc, ha, hu]
  · rw [mul_left_fst, Hom.mul_def (fst G G), Hom.inv_def (snd G G), Over.comp_left (f := lift (fst G G) (snd G G ≫ ι)),
      ← Category.assoc]
    congr 1
    apply ext_tensor
    · rw [lift_μ_fst, Category.assoc, ← Over.comp_left, lift_fst, hΦ1, Over.id_left, Category.id_comp]
    · rw [lift_μ_snd, Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc,
        inv_left_fst, ← Category.assoc a.left, ha, hu, Over.comp_left, reassoc_of% hΦ2]

end GlobalTheory.TransBaseChange
