import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private noncomputable def invFn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Ob b A ⥤ Ob a A where
  obj y := ⟨(Equiv.ofBijective _ h1).symm y.pt⟩
  map {x y} f := ⟨(Equiv.ofBijective _ h2).symm f.1, h1.1 (by
    have e1 : φ.d.app A ((Equiv.ofBijective _ h1).symm x.pt) = x.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e2 : φ.d.app A ((Equiv.ofBijective _ h1).symm y.pt) = y.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm f.1) = f.1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.d.app A _ = φ.d.app A _
    rw [φ.eq, e1, e2, e3]
    exact f.2)⟩
  map_id x := Subtype.ext (h2.1 (by
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm 1) = 1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A 1
    rw [map_one (φ.g.app A).hom]
    exact e3))
  map_comp {x y z} f g := Subtype.ext (h2.1 (by
    have e : ∀ u : b.G.obj A, φ.g.app A ((Equiv.ofBijective _ h2).symm u) = u := fun u =>
      (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A (_ * _)
    rw [map_mul (φ.g.app A).hom, e, e, e]
    rfl))

private theorem fn_inv {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    φ.fn A ⋙ invFn φ A h1 h2 = 𝟭 _ := by
  have ho : ∀ x : Ob a A, (φ.fn A ⋙ invFn φ A h1 h2).obj x = (𝟭 _ : Ob a A ⥤ Ob a A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).symm_apply_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).symm_apply_apply f.1

private theorem inv_fn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    invFn φ A h1 h2 ⋙ φ.fn A = 𝟭 _ := by
  have ho : ∀ x : Ob b A, (invFn φ A h1 h2 ⋙ φ.fn A).obj x = (𝟭 _ : Ob b A ⥤ Ob b A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).apply_symm_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).apply_symm_apply f.1

private theorem comp_bij {C D : Type} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) (G : D ⥤ C)
    (h : F ⋙ G = 𝟭 _) (h' : G ⋙ F = 𝟭 _) (k : ℕ) :
    Function.Bijective (fun s : ComposableArrows C k => s ⋙ F) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun t => t ⋙ G, fun s => ?_, fun t => ?_⟩
  · show (s ⋙ F) ⋙ G = s
    rw [Functor.assoc, h, Functor.comp_id]
  · show (t ⋙ G) ⋙ F = t
    rw [Functor.assoc, h', Functor.comp_id]

theorem UpperTheory.isIso_stackProductMap_of_bijective :
    ∀ (E : Spc) {a b : Act} (φ : Act.Hom a b), (∀ A, Function.Bijective (fun x : a.D.obj A => φ.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) → IsIso (Sp.map E φ) := by
  intro E a b φ h1 h2
  apply isIso_of_bijective_on_simplices
  intro k T
  have hb := (Function.bijective_id (α := Sx E k T)).prodMap
    (comp_bij (C := Ob a (Scheme.Γ.obj (op T))) (D := Ob b (Scheme.Γ.obj (op T)))
      (φ.fn _) (invFn φ _ (h1 _) (h2 _)) (fn_inv φ _ (h1 _) (h2 _)) (inv_fn φ _ (h1 _) (h2 _)) k)
  exact hb
