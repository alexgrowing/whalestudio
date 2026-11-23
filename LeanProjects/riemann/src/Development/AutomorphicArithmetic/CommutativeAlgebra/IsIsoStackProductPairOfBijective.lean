import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.InverseDerivation

variable {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c) (A : CommRingCat.{0})

private abbrev BD : Prop :=
  Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))

private abbrev BG : Prop :=
  Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))

variable {ρ σ A}

private noncomputable def invD (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : a.D.obj A :=
  (Equiv.ofBijective _ hd).symm p

private noncomputable def invG (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : a.G.obj A :=
  (Equiv.ofBijective _ hg).symm p

private theorem invD_fst (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : ρ.d.app A (invD hd p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invD_snd (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : σ.d.app A (invD hd p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invG_fst (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : ρ.g.app A (invG hg p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invG_snd (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : σ.g.app A (invG hg p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invD_eq (hd : BD ρ σ A) {x : a.D.obj A} {p : b.D.obj A × c.D.obj A}
    (h1 : ρ.d.app A x = p.1) (h2 : σ.d.app A x = p.2) : invD hd p = x := by
  apply hd.1
  refine (Equiv.ofBijective_apply_symm_apply _ hd p).trans ?_
  exact Prod.ext h1.symm h2.symm

private theorem invG_eq (hg : BG ρ σ A) {x : a.G.obj A} {p : b.G.obj A × c.G.obj A}
    (h1 : ρ.g.app A x = p.1) (h2 : σ.g.app A x = p.2) : invG hg p = x := by
  apply hg.1
  refine (Equiv.ofBijective_apply_symm_apply _ hg p).trans ?_
  exact Prod.ext h1.symm h2.symm

private noncomputable def lift (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) : J ⥤ Ob a A where
  obj j := ⟨invD hd ((y.obj j).pt, (z.obj j).pt)⟩
  map {i j} f := ⟨invG hg ((y.map f).1, (z.map f).1), by
    refine hd.1 (Prod.ext ?_ ?_)
    · change ρ.d.app A _ = ρ.d.app A (a.smul A _ _)
      rw [ρ.eq, invD_fst, invD_fst, invG_fst]
      exact (y.map f).2
    · change σ.d.app A _ = σ.d.app A (a.smul A _ _)
      rw [σ.eq, invD_snd, invD_snd, invG_snd]
      exact (z.map f).2⟩
  map_id j := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A 1 = (y.map (𝟙 j)).1
      rw [y.map_id]
      exact map_one (ρ.g.app A).hom
    · change σ.g.app A 1 = (z.map (𝟙 j)).1
      rw [z.map_id]
      exact map_one (σ.g.app A).hom
  map_comp {i j l} f g := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A (invG hg _ * invG hg _) = (y.map (f ≫ g)).1
      rw [y.map_comp]
      refine (map_mul (ρ.g.app A).hom _ _).trans ?_
      change ρ.g.app A _ * ρ.g.app A _ = _
      rw [invG_fst, invG_fst]
      rfl
    · change σ.g.app A (invG hg _ * invG hg _) = (z.map (f ≫ g)).1
      rw [z.map_comp]
      refine (map_mul (σ.g.app A).hom _ _).trans ?_
      change σ.g.app A _ * σ.g.app A _ = _
      rw [invG_snd, invG_snd]
      rfl

private theorem lift_fst (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ ρ.fn A = y := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
    rw [invD_fst]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨ρ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob b A) = y.obj i
      rw [invD_fst]
    · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
      rw [invD_fst]
    · change ρ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (y.map f).1
      rw [invG_fst]

private theorem lift_snd (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ σ.fn A = z := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
    rw [invD_snd]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨σ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob c A) = z.obj i
      rw [invD_snd]
    · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
      rw [invD_snd]
    · change σ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (z.map f).1
      rw [invG_snd]

private theorem lift_comp (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (w : J ⥤ Ob a A) :
    lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) = w := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
    rw [invD_eq hd rfl rfl]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨invD hd (ρ.d.app A (w.obj i).pt, σ.d.app A (w.obj i).pt)⟩ : Ob a A) = w.obj i
      rw [invD_eq hd rfl rfl]
    · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
      rw [invD_eq hd rfl rfl]
    · change invG hg (ρ.g.app A (w.map f).1, σ.g.app A (w.map f).1) = (w.map f).1
      exact invG_eq hg rfl rfl

private theorem comp_inj (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] {w w' : J ⥤ Ob a A}
    (h1 : w ⋙ ρ.fn A = w' ⋙ ρ.fn A) (h2 : w ⋙ σ.fn A = w' ⋙ σ.fn A) : w = w' := by
  calc w = lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) := (lift_comp hd hg w).symm
    _ = lift hd hg (w' ⋙ ρ.fn A) (w' ⋙ σ.fn A) := by rw [h1, h2]
    _ = w' := lift_comp hd hg w'

end UpperTheory.InverseDerivation

open UpperTheory.InverseDerivation in
theorem UpperTheory.isIso_stackProductPair_of_bijective :
    ∀ (E : Spc) {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c),
        (∀ A, Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))) →
        IsIso (Sp.pair E ρ σ) := by
  intro E a b c ρ σ hd hg
  refine isIso_of_bijective_on_simplices _ (fun k T => ?_)
  let A : CommRingCat := Scheme.Γ.obj (op T)
  change Function.Bijective
    (fun p : (E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob a A) =>
      (((p.1, p.2 ⋙ ρ.fn A), p.2 ⋙ σ.fn A) :
        ((E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob b A)) × (Fin (k+1) ⥤ Ob c A)))
  refine ⟨fun p q h => ?_, fun q => ?_⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext h1 (comp_inj (hd A) (hg A) h2 h3)
  · refine ⟨(q.1.1, lift (hd A) (hg A) q.1.2 q.2), ?_⟩
    simp only [lift_fst, lift_snd]
