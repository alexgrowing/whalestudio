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
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjBundleFormulaIffPglForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.W1

variable {q : ℕ}

private theorem cast_cast {X : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q X n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4
  rfl

private theorem cup_one' [NeZero q] {X : Spc} (hX : Inv q X) {n i : ℤ} (x : Ht q X n i) :
    cup q x (one q X) = x.cast (by ring) (by ring) := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q X x (one q X), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 X hX x, cast_cast, mul_zero, Int.negOnePow_zero, one_smul]

private theorem cup_one_cast [NeZero q] {X : Spc} (hX : Inv q X) {n i m j : ℤ} (x : Ht q X n i) (hm : 0 = m) (hj : 0 = j) :
    cup q x ((one q X).cast hm hj) = x.cast (by omega) (by omega) := by
  subst hm hj
  exact cup_one' hX x

private theorem bij_of_cast {X E : Spc} (π : X ⟶ E) {n i n' i' : ℤ} (hn : n' = n) (hi : i' = i)
    (h : Function.Bijective fun x : Ht q E n' i' => (Ht.cast hn hi (pull _ π _ _ x) : Ht q X n i)) :
    Function.Bijective (pull _ π (tw q i) n) := by
  subst hn hi
  exact h

private theorem eqv_comp {R : Type} [CommRing R] {X Y Z : Spc} {f : X ⟶ Y} {g : Y ⟶ Z} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have e : (pull R (f ≫ g) F n : H R Z F n → H R X F n) = pull R f F n ∘ pull R g F n :=
    funext (pull_comp R f g F n)
  rw [e]
  exact (hf n).comp (hg n)

private theorem eqv_iso {R : Type} [CommRing R] {X Y : Spc} (f : X ⟶ Y) [IsIso f] (F : Shv R) : Eqv R f F := fun n => by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem inv_sp {E : Spc} (hE : Inv q E) (a : Act) : Inv q (Sp E a) :=
  fun U ⟨x⟩ => hE U ⟨((Sp.fst E a).app _).app _ x⟩

private theorem equiv_first_twist [NeZero q] (E : Spc) (hE : Inv q E) (i : ℤ) : Eqv _ (Sp.fst E (XC 1)) (tw q i) := by
  have hP : Pbf q E 1 := (UpperTheory.projBundleFormula_iff_pglForm q E 1 hE).1 (UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q E hE)
  have hX : Inv q (Sp E (XC 1)) := inv_sp hE _
  intro n
  have h := hP n i
  have hn : n - 2 * (((0 : Fin 1) : ℕ) : ℤ) = n := by simp
  have hi : i - (((0 : Fin 1) : ℕ) : ℤ) = i := by simp
  have hform : ∀ a : ∀ j : Fin 1, Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ)),
      ∑ j : Fin 1, ((cup q (pull _ (Sp.fst E (XC 1)) _ _ (a j)) (cpow q (c1 q (Sp.line E (chiX 1))) j)).cast (by ring) (by ring) :
        Ht q (Sp E (XC 1)) n i) =
      Ht.cast hn hi (pull _ (Sp.fst E (XC 1)) _ _ (a 0)) := by
    intro a
    rw [Fin.sum_univ_one]
    have h0 : cpow q (c1 q (Sp.line E (chiX 1))) ((0 : Fin 1) : ℕ) = (one q _).cast (by simp) (by simp) := cpow_zero q _
    rw [h0, cup_one_cast hX, cast_cast]
  simp only [hform] at h
  refine bij_of_cast _ hn hi ?_
  let e := Equiv.piUnique fun j : Fin 1 => Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ))
  have e2 : ∀ x, (e.symm x) 0 = x := fun x => e.apply_symm_apply x
  have h3 := h.comp e.symm.bijective
  have h4 : ((fun a : ∀ j : Fin 1, Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ)) =>
      (Ht.cast hn hi (pull _ (Sp.fst E (XC 1)) _ _ (a 0)) : Ht q (Sp E (XC 1)) n i)) ∘ e.symm) =
      fun x => Ht.cast hn hi (pull _ (Sp.fst E (XC 1)) _ _ x) := by
    funext x
    simp only [Function.comp_apply]
    rw [e2]
  rw [h4] at h3
  exact h3

private def invU {A : Type} [CommRing A] (a : A) (h : IsUnit a) : A := ((h.unit⁻¹ : Aˣ) : A)

private theorem mul_invU {A : Type} [CommRing A] (a : A) (h : IsUnit a) : a * invU a h = 1 :=
  h.mul_val_inv

private theorem invU_eq {A : Type} [CommRing A] {a b : A} (h : IsUnit a) (e : a * b = 1) : invU a h = b :=
  Units.inv_eq_of_mul_eq_one_right e

private theorem um_top {N : ℕ} {A : Type} [CommRing A] (v : Fin N → A) (k : Fin N) (h : IsUnit (v k)) :
    Ideal.span (Set.range v) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k, rfl⟩) h

private def tl {M : ℕ} {A : Type} [CommRing A] (v : Um (M + 2) A) (h : IsUnit (v.1 (Fin.last (M + 1)))) : Um (M + 1) A :=
  ⟨Fin.tail v.1, um_top _ (Fin.last M) h⟩

private def rho (M : ℕ) : Act.Hom ((XC (M + 2)).sub (Q1 (M + 1))) ((XC (M + 1)).sub (Q1 M)) where
  d :=
    { app := fun A => TypeCat.ofHom fun x => ⟨tl (A := A) x.1 x.2, x.2⟩
      naturality := fun _ _ _ => rfl }
  g := 𝟙 gmF
  eq _ _ _ := rfl

private theorem sig_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a t : A) (h : IsUnit t) (h' : IsUnit (f t)) :
    f (a * invU t h) = f a * invU (f t) h' := by
  rw [map_mul, invU_eq h' (b := f (invU t h)) (by rw [← map_mul, mul_invU, map_one])]

private theorem sig_inv {A : Type} [CommRing A] (u : Aˣ) (a t : A) (h : IsUnit t) (h' : IsUnit ((u : A) * t)) :
    ((u : A) * a) * invU ((u : A) * t) h' = a * invU t h := by
  rw [invU_eq h' (b := ((u⁻¹ : Aˣ) : A) * invU t h) (by
    have e := mul_invU t h
    calc (u : A) * t * (((u⁻¹ : Aˣ) : A) * invU t h) = ((u : A) * ((u⁻¹ : Aˣ) : A)) * (t * invU t h) := by ring
      _ = 1 := by rw [e]; simp)]
  calc (u : A) * a * (((u⁻¹ : Aˣ) : A) * invU t h) = ((u : A) * ((u⁻¹ : Aˣ) : A)) * (a * invU t h) := by ring
    _ = a * invU t h := by simp

private def sig (M : ℕ) : Act.Hom ((XC (M + 2)).sub (Q1 (M + 1))) affC where
  d :=
    { app := fun A => TypeCat.ofHom fun x =>
        (show Um (M + 2) A from x.1).1 0 * invU _ x.2
      naturality := fun A B f => by
        ext x
        exact (sig_nat f.hom _ _ x.2 _).symm }
  g := { app := fun A => GrpCat.ofHom 1, naturality := fun _ _ _ => rfl }
  eq A u x := sig_inv (A := A) u _ _ x.2 _

private theorem bij_plain (M : ℕ) (A : Type) [CommRing A] :
    Function.Bijective (fun x : {v : Um (M + 2) A // IsUnit (v.1 (Fin.last (M + 1)))} =>
      (((⟨tl x.1 x.2, x.2⟩ : {w : Um (M + 1) A // IsUnit (w.1 (Fin.last M))})), x.1.1 0 * invU _ x.2)) := by
  constructor
  · intro x y h
    have h1 : Fin.tail x.1.1 = Fin.tail y.1.1 := congrArg (fun z => z.1.1) (congrArg Prod.fst h)
    have h2 : x.1.1 0 * invU _ x.2 = y.1.1 0 * invU _ y.2 := congrArg Prod.snd h
    have ht : x.1.1 (Fin.last (M + 1)) = y.1.1 (Fin.last (M + 1)) := congrFun h1 (Fin.last M)
    have h0 : x.1.1 0 = y.1.1 0 := by
      have e1 : x.1.1 0 * invU _ x.2 * x.1.1 (Fin.last (M + 1)) = x.1.1 0 := by
        rw [mul_assoc, mul_comm (invU _ _), mul_invU, mul_one]
      have e2 : y.1.1 0 * invU _ y.2 * y.1.1 (Fin.last (M + 1)) = y.1.1 0 := by
        rw [mul_assoc, mul_comm (invU _ _), mul_invU, mul_one]
      rw [← e1, ← e2, h2, ht]
    refine Subtype.ext (Subtype.ext (funext fun k => ?_))
    exact Fin.cases h0 (fun j => congrFun h1 j) k
  · rintro ⟨w, r⟩
    have hw : IsUnit ((Fin.cons (r * w.1.1 (Fin.last M)) w.1.1 : Fin (M + 2) → A) (Fin.last (M + 1))) := by
      rw [← Fin.succ_last, Fin.cons_succ]
      exact w.2
    refine ⟨⟨⟨Fin.cons (r * w.1.1 (Fin.last M)) w.1.1, um_top _ _ hw⟩, hw⟩, Prod.ext ?_ ?_⟩
    · exact Subtype.ext (Subtype.ext (funext fun k => rfl))
    · change (Fin.cons (r * w.1.1 (Fin.last M)) w.1.1 : Fin (M + 2) → A) 0 * invU _ hw = r
      have e : (Fin.cons (r * w.1.1 (Fin.last M)) w.1.1 : Fin (M + 2) → A) (Fin.last (M + 1)) = w.1.1 (Fin.last M) := by
        rw [← Fin.succ_last, Fin.cons_succ]
      rw [Fin.cons_zero, invU_eq hw (b := invU _ w.2) (by rw [e, mul_invU]), mul_assoc, mul_invU, mul_one]

private theorem bij_grp (M : ℕ) (A : CommRingCat.{0}) :
    Function.Bijective (fun g : ((XC (M + 2)).sub (Q1 (M + 1))).G.obj A =>
      (((rho M).g.app A g, (sig M).g.app A g) : ((XC (M + 1)).sub (Q1 M)).G.obj A × affC.G.obj A)) := by
  constructor
  · intro x y h
    exact congrArg Prod.fst h
  · rintro ⟨g, u⟩
    exact ⟨g, rfl⟩

private theorem bij_incl0 (A : CommRingCat.{0}) :
    Function.Bijective (fun x : ((XC 1).sub (Q1 0)).D.obj A => (incl (Q1 0)).d.app A x) := by
  refine ⟨fun x y h => Subtype.ext h, fun v => ⟨⟨v, ?_⟩, rfl⟩⟩
  have h : Ideal.span (Set.range (show Um 1 A from v).1) = ⊤ := (show Um 1 A from v).2
  have hr : Set.range (show Um 1 A from v).1 = {(show Um 1 A from v).1 0} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i 0]
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [hr] at h
  exact Ideal.span_singleton_eq_top.1 h

end UpperTheory.W1

end

open UpperTheory.W1 in
theorem UpperTheory.eqv_twist_unimodularUnitLocus :
    ∀ (q : ℕ) [NeZero q] (M : ℕ) (E : Spc) (i : ℤ), Inv q E →
        Eqv _ (Sp.map E (incl (Q1 M)) ≫ Sp.fst E (XC (M + 1))) (tw q i) := by
  intro q _ M E i hE
  induction M with
  | zero =>
    haveI : IsIso (Sp.map E (incl (Q1 0))) :=
      UpperTheory.isIso_stackProductMap_of_bijective E (incl (Q1 0)) bij_incl0 (fun A => Function.bijective_id)
    exact eqv_comp (eqv_iso _ _) (equiv_first_twist E hE i)
  | succ M ih =>
    haveI : IsIso (Sp.pair E (rho M) (sig M)) :=
      UpperTheory.isIso_stackProductPair_of_bijective E (rho M) (sig M) (fun A => bij_plain M A) (bij_grp M)
    have e : Sp.map E (incl (Q1 (M + 1))) ≫ Sp.fst E (XC (M + 1 + 1)) =
        Sp.pair E (rho M) (sig M) ≫ Sp.fst (Sp E ((XC (M + 1)).sub (Q1 M))) affC ≫
          Sp.map E (incl (Q1 M)) ≫ Sp.fst E (XC (M + 1)) := rfl
    rw [e]
    exact eqv_comp (eqv_iso _ _) (eqv_comp (UpperTheory.affineLineAction_fst_twistEquiv q _ i (inv_sp hE _)) ih)
