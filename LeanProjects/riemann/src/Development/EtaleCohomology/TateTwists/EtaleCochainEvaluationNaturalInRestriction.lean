import Development.EtaleCohomology.TateTwists.UnitClassSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCochainEvaluationNaturalInRestriction : Prop :=
  ∀ {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U),
    ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) = Sec.res g (ev α p s h U x)

def UnitClassExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ

def UnitClassUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ α β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) →
    (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev β.1 0 0 (by simp) U x = resGen 0 ζ) →
    CohomologyClass.mk α = CohomologyClass.mk β

def DegreeZeroCocyclePullback : Prop :=
  ∀ {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (α : Cocycle ((chains R).obj E') (res R F) 0),
    ∃ β : Cocycle ((chains R).obj E) (res R F) 0, pull R f F 0 (CohomologyClass.mk α) = CohomologyClass.mk β ∧
      ∀ (U : Scheme.{0}) (x : Sx E 0 U),
        ev β.1 0 0 (by simp) U x = ev α.1 0 0 (by simp) U ((f.app (op (SimplexCategory.mk 0))).app (op U) x)

theorem freeGen_nat {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  have hm : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up (P.map g.op x)) := by
    simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]; erw [ModuleCat.free_map_apply]; rfl
  exact h.symm.trans (congrArg (toSheafify Scheme.etaleTopology ((freeP R).obj P) |>.app (op V)).hom hm)

theorem ev_nat_pf : EtaleCochainEvaluationNaturalInRestriction := by
  intro R _ E I n α p s h V U g x
  unfold ev
  rw [← freeGen_nat]
  have key := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at key
  exact key

end LateralTheory.EtaleFoundations
