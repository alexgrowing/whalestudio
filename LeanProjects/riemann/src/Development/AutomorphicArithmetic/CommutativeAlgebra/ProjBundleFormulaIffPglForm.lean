import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.PullPf

private def unitOf {M : ℕ} {A : CommRingCat.{0}} {x y : Ob (XC M) A} (f : x ⟶ y) : (A : Type)ˣ := f.1

private def vec {M : ℕ} {A : CommRingCat.{0}} (x : Ob (XC M) A) : Fin M → A := (show Um M A from x.pt).1

private theorem unitOf_spec {M : ℕ} {A : CommRingCat.{0}} {x y : Ob (XC M) A} (f : x ⟶ y) (i : Fin M) :
    vec x i = (unitOf f : A) * vec y i :=
  congrFun (congrArg Subtype.val f.2) i

private def tauF (M : ℕ) (A : CommRingCat.{0}) : Ob (XC M) A ⥤ Um M A where
  obj x := x.pt
  map {x y} f := ⟨(1, unitOf f), by
    change ((1 : GL (Fin M) A) : Matrix (Fin M) (Fin M) A).mulVec (vec x) = (unitOf f : A) • vec y
    funext i
    simpa using unitOf_spec f i⟩
  map_id x := Subtype.ext rfl
  map_comp {x y z} f g := Subtype.ext (Prod.ext (mul_one _).symm (mul_comm _ _))

private def tau (M : ℕ) : (XC M).cat ⟶ pglCat M where
  app A := (tauF M A).toCatHom
  naturality {A B} f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
    refine Subtype.ext (Prod.ext ?_ rfl)
    exact (map_one (Matrix.GeneralLinearGroup.map f.hom)).symm

private def tauS (M : ℕ) : spc (XC M) ⟶ PGL M := ofCatMap (tau M)

private theorem sq (S : Spc) (M : ℕ) :
    Sp.fst S (XC M) ≫ triv S M = (Sp.snd S (XC M) ≫ tauS M) ≫ PGL.pr M := by
  ext k T x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun a b h => ?_)
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem um_hom_val {M : ℕ} {A : Type} [CommRing A] {v v' w w' : Um M A} (hv : v = v') (hw : w = w')
    (f : v ⟶ w) (f' : v' ⟶ w') (h : HEq f f') : f.1 = f'.1 := by
  subst hv hw
  rw [eq_of_heq h]

private theorem tau_inj {M k : ℕ} {A : CommRingCat.{0}} (w w' : Fin (k + 1) ⥤ Ob (XC M) A)
    (h : w ⋙ tauF M A = w' ⋙ tauF M A) : w = w' := by
  have ho : ∀ i, w.obj i = w'.obj i := fun i => by
    have := congrArg (fun F : Fin (k + 1) ⥤ Um M A => F.obj i) h
    exact congrArg Ob.mk this
  refine CategoryTheory.Functor.hext ho (fun a b f => Ob.hom_heq (ho a) (ho b) _ _ ?_)
  have hh : HEq ((w ⋙ tauF M A).map f) ((w' ⋙ tauF M A).map f) := by rw [h]
  have := um_hom_val (congrArg Ob.pt (ho a)) (congrArg Ob.pt (ho b)) _ _ hh
  exact congrArg Prod.snd this

private theorem tau_surj {M k : ℕ} {A : CommRingCat.{0}} (y : Fin (k + 1) ⥤ Um M A)
    (hy : y ⋙ Um.toGL M A = (Functor.const _).obj (SingleObj.star _)) :
    ∃ w : Fin (k + 1) ⥤ Ob (XC M) A, w ⋙ tauF M A = y := by
  have h1 : ∀ {a b : Fin (k + 1)} (f : a ⟶ b), (y.map f).1.1 = 1 := fun {a b} f => by
    have := Functor.congr_hom hy f
    erw [eqToHom_refl, Category.id_comp, Category.comp_id] at this
    exact this
  refine ⟨{ obj := fun i => ⟨y.obj i⟩
            map := fun {a b} f => ⟨show (XC M).G.obj A from (y.map f).1.2, ?_⟩
            map_id := fun a => ?_
            map_comp := fun {a b c} f g => ?_ }, ?_⟩
  · refine Subtype.ext (funext fun i => ?_)
    have := congrFun (y.map f).2 i
    rw [h1 f] at this
    have h2 : (y.obj a).1 i = ((y.map f).1.2 : A) * (y.obj b).1 i := by simpa using this
    exact h2
  · refine Subtype.ext ?_
    change (y.map (𝟙 a)).1.2 = 1
    rw [y.map_id]
    rfl
  · refine Subtype.ext ?_
    change (y.map (f ≫ g)).1.2 = (y.map f).1.2 * (y.map g).1.2
    rw [y.map_comp, mul_comm]
    rfl
  · refine CategoryTheory.Functor.hext (fun _ => rfl) (fun a b f => heq_of_eq ?_)
    exact Subtype.ext (Prod.ext (h1 f).symm rfl)

private def uMap (S : Spc) (M : ℕ) : Sp S (XC M) ⟶ pullback (triv S M) (PGL.pr M) :=
  pullback.lift (Sp.fst S (XC M)) (Sp.snd S (XC M) ≫ tauS M) (sq S M)

private theorem sx_comp {X Y Z : Spc} (f : X ⟶ Y) (g : Y ⟶ Z) {k : ℕ} {T : Scheme.{0}} (x : Sx X k T) :
    Sx.map g (Sx.map f x) = Sx.map (f ≫ g) x := rfl

private theorem u_fst (S : Spc) (M : ℕ) {k : ℕ} {T : Scheme.{0}} (c : Sx (Sp S (XC M)) k T) :
    Sx.map (pullback.fst _ _) (Sx.map (uMap S M) c) = c.1 := by
  rw [sx_comp, uMap, pullback.lift_fst]
  rfl

private theorem u_snd (S : Spc) (M : ℕ) {k : ℕ} {T : Scheme.{0}} (c : Sx (Sp S (XC M)) k T) :
    Sx.map (pullback.snd _ _) (Sx.map (uMap S M) c) = Sx.map (tauS M) c.2 := by
  rw [sx_comp, uMap, pullback.lift_snd]
  rfl

private instance isIso_u (S : Spc) (M : ℕ) : IsIso (uMap S M) := by
  refine UpperTheory.isIso_of_bijective_on_simplices _ fun k T => ⟨fun a b h => ?_, fun z => ?_⟩
  · have h1 := congrArg (Sx.map (pullback.fst _ _)) h
    have h2 := congrArg (Sx.map (pullback.snd _ _)) h
    rw [u_fst, u_fst] at h1
    rw [u_snd, u_snd] at h2
    exact Prod.ext h1 (tau_inj _ _ h2)
  · have hc : Sx.map (triv S M) (Sx.map (pullback.fst _ _) z) = Sx.map (PGL.pr M) (Sx.map (pullback.snd _ _) z) := by
      rw [sx_comp, sx_comp, pullback.condition]
    obtain ⟨w, hw⟩ := tau_surj (M := M) (k := k) (A := Scheme.Γ.obj (op T))
      (Sx.map (pullback.snd (triv S M) (PGL.pr M)) z) hc.symm
    refine ⟨(Sx.map (pullback.fst _ _) z, w), ?_⟩
    obtain ⟨z0, -, hu⟩ := UpperTheory.simplices_pullback_existsUnique_of_map_eq (triv S M) (PGL.pr M) k T _ _ hc
    exact (hu _ ⟨u_fst S M (Sx.map (pullback.fst _ _) z, w), (u_snd S M (Sx.map (pullback.fst _ _) z, w)).trans hw⟩).trans
      (hu z ⟨rfl, rfl⟩).symm

private theorem tau_line (M : ℕ) : tauS M ≫ PGL.line M = lineOf (chiX M) := rfl

private theorem u_line (S : Spc) (M : ℕ) :
    uMap S M ≫ pullback.snd _ _ ≫ PGL.line M = Sp.line S (chiX M) := by
  rw [← Category.assoc, uMap, pullback.lift_snd, Category.assoc, tau_line]

end UpperTheory.PullPf

open UpperTheory.PullPf in
theorem UpperTheory.projBundleFormula_iff_pglForm :
    ∀ (q : ℕ) [NeZero q] (S : Spc) (M : ℕ), Inv q S → (PBF q S M ↔ Pbf q S M) := by
  intro q _ S M hS
  have hP : Inv q (pullback (triv S M) (PGL.pr M)) := fun U ⟨x⟩ => hS U ⟨Sx.map (pullback.fst _ _) x⟩
  have hX : Inv q (Sp S (XC M)) := fun U ⟨x⟩ => hS U ⟨x.1⟩
  have hf : uMap S M ≫ pullback.fst _ _ = Sp.fst S (XC M) := pullback.lift_fst _ _ _
  constructor
  · intro h
    have h1 := UpperTheory.lerayHirsch_of_iso_square q (pullback.fst _ _) (Sp.fst S (XC M)) (uMap S M) (𝟙 S)
      (by rw [hf, Category.comp_id]) _ _ _ h
    have e : ∀ j : ℕ, pull _ (uMap S M) (tw q (j : ℤ)) (2 * (j : ℤ))
        (cpow q (c1 q (pullback.snd (triv S M) (PGL.pr M) ≫ PGL.line M)) j) =
        cpow q (c1 q (Sp.line S (chiX M))) j := fun j => by
      rw [UpperTheory.pull_cupPow_eq_cupPow_pull q _ _ j hP, (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hP, u_line]
    unfold Pbf
    simpa only [e] using h1
  · intro h
    have h1 := UpperTheory.lerayHirsch_of_iso_square q (Sp.fst S (XC M)) (pullback.fst _ _) (inv (uMap S M)) (𝟙 S)
      (by rw [Category.comp_id, IsIso.inv_comp_eq, hf]) _ _ _ h
    have e : ∀ j : ℕ, pull _ (inv (uMap S M)) (tw q (j : ℤ)) (2 * (j : ℤ))
        (cpow q (c1 q (Sp.line S (chiX M))) j) =
        cpow q (c1 q (pullback.snd (triv S M) (PGL.pr M) ≫ PGL.line M)) j := fun j => by
      rw [UpperTheory.pull_cupPow_eq_cupPow_pull q _ _ j hX, (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hX, ← u_line, IsIso.inv_hom_id_assoc]
    unfold PBF
    simpa only [e] using h1

end
