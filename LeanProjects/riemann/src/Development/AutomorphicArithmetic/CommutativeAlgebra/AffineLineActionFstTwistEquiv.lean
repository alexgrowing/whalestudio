import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistAffineLineProjectionEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.LineAct

open Polynomial

private def coord {T : Scheme.{0}} (f : T ⟶ Pbf.A1) : Γ(T, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

private theorem coord_comp {T' T : Scheme.{0}} (g : T' ⟶ T) (f : T ⟶ Pbf.A1) :
    coord (g ≫ f) = g.appTop.hom (coord f) := by
  simp [coord]
  rfl

private theorem eq_of_appTop {T : Scheme.{0}} (f : T ⟶ Pbf.A1) :
    f = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv ≫ f.appTop) := by
  have h := Scheme.toSpecΓ_naturality f
  have h2 : (Spec (CommRingCat.of ℤ[X])).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv = 𝟙 _ := by
    rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    simp
  calc f = f ≫ (Spec (CommRingCat.of ℤ[X])).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv := by
        rw [h2, Category.comp_id]
    _ = _ := by
        rw [← Category.assoc, h, Category.assoc, ← Spec.map_comp]

private theorem coord_bij (T : Scheme.{0}) : Function.Bijective (coord (T := T)) := by
  constructor
  · intro f g h
    rw [eq_of_appTop f, eq_of_appTop g]
    congr 2
    apply CommRingCat.hom_ext
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    exact h
  · intro a
    refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (eval₂RingHom (Int.castRingHom _) a)), ?_⟩
    simp [coord, Scheme.toSpecΓ_appTop]

private theorem chain_ext {A : CommRingCat.{0}} {n : ℕ} (x y : Fin (n + 1) ⥤ Ob affC A)
    (h : ∀ i, (x.obj i).pt = (y.obj i).pt) : x = y := by
  have ho : ∀ i, x.obj i = y.obj i := fun i => by
    have := h i
    cases hx : x.obj i
    cases hy : y.obj i
    simp_all
  refine CategoryTheory.Functor.ext ho (fun i j f => ?_)
  exact Subtype.ext (Subsingleton.elim (α := PUnit) _ _)

private theorem chain_pt {A : CommRingCat.{0}} {n : ℕ} (x : Fin (n + 1) ⥤ Ob affC A) (i : Fin (n + 1)) :
    (x.obj i).pt = (x.obj 0).pt :=
  ((x.map (homOfLE (Fin.zero_le i))).2).symm

private def lineMap : sch.obj Pbf.A1 ⟶ spc affC where
  app k :=
    { app := fun T => TypeCat.ofHom fun f =>
        (show Fin (k.unop.len + 1) ⥤ Ob affC Γ(T.unop, ⊤) from
          (Functor.const _).obj ⟨coord (show T.unop ⟶ Pbf.A1 from f)⟩)
      naturality := fun T T' g => by
        ext f
        refine chain_ext _ _ fun i => ?_
        exact coord_comp g.unop (show T.unop ⟶ Pbf.A1 from f) }
  naturality m n f := by
    ext T x
    rfl

private theorem lineMap_bij (k : ℕ) (T : Scheme.{0}) :
    Function.Bijective (fun x : Sx (sch.obj Pbf.A1) k T => x.map lineMap) := by
  constructor
  · intro f g h
    refine (coord_bij T).1 ?_
    exact congrArg (fun c : Fin (k + 1) ⥤ Ob affC Γ(T, ⊤) => (c.obj 0).pt) h
  · intro y
    obtain ⟨f, hf⟩ := (coord_bij T).2 ((show Fin (k + 1) ⥤ Ob affC Γ(T, ⊤) from y).obj 0).pt
    refine ⟨f, ?_⟩
    refine chain_ext _ _ fun i => ?_
    exact hf.trans (chain_pt (show Fin (k + 1) ⥤ Ob affC Γ(T, ⊤) from y) i).symm

private theorem mulS_hom_ext {X E Z : Spc} {f g : X ⟶ mulS E Z}
    (h1 : f ≫ mulS.fst E Z = g ≫ mulS.fst E Z) (h2 : f ≫ mulS.snd E Z = g ≫ mulS.snd E Z) : f = g := by
  ext k T x
  have a := ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h1 k) T) x
  have b := ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h2 k) T) x
  exact Prod.ext a b

end UpperTheory.LineAct

end

open UpperTheory.LineAct in
theorem UpperTheory.affineLineAction_fst_twistEquiv :
    ∀ (q : ℕ) [NeZero q] (S : Spc) (i : ℤ), Inv q S → Eqv _ (Sp.fst S affC) (tw q i) := by
  intro q _ S i hS
  haveI : IsIso lineMap := UpperTheory.isIso_of_bijective_on_simplices lineMap lineMap_bij
  let u : sch.obj Pbf.A1 ⨯ S ⟶ Sp S affC := mulS.lift prod.snd (prod.fst ≫ lineMap)
  let v : Sp S affC ⟶ sch.obj Pbf.A1 ⨯ S := prod.lift (Sp.snd S affC ≫ inv lineMap) (Sp.fst S affC)
  have hu1 : u ≫ mulS.fst _ _ = prod.snd := rfl
  have hu2 : u ≫ mulS.snd _ _ = prod.fst ≫ lineMap := rfl
  have huv : u ≫ v = 𝟙 _ := by
    apply Limits.prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, ← Category.assoc, hu2]
      simp
    · rw [Category.assoc, prod.lift_snd, Category.id_comp]
      exact hu1
  have hvu : v ≫ u = 𝟙 _ := by
    apply mulS_hom_ext
    · rw [Category.assoc, hu1, prod.lift_snd, Category.id_comp]
    · rw [Category.assoc, hu2, ← Category.assoc, prod.lift_fst]
      simp
  have hpu : ∀ n, Function.Bijective (pull (ZMod q) u (tw q i) n) := fun n =>
    Function.bijective_iff_has_inverse.2 ⟨pull _ v (tw q i) n, fun x => by
      rw [← pull_comp, hvu, pull_id], fun x => by
      rw [← pull_comp, huv, pull_id]⟩
  intro n
  have h := UpperTheory.tateTwist_affineLine_projection_equiv q S i hS n
  have e : (⇑(pull (ZMod q) (prod.snd : sch.obj Pbf.A1 ⨯ S ⟶ S) (tw q i) n)) =
      (pull (ZMod q) u (tw q i) n) ∘ (pull (ZMod q) (Sp.fst S affC) (tw q i) n) := by
    funext x
    rw [← hu1]
    exact pull_comp _ u _ _ n x
  rw [e] at h
  exact (Function.Bijective.of_comp_iff' (hpu n) _).1 h
