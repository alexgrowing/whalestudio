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

namespace UpperTheory.ProjectiveLineCharts

private def prD (b : Act) : CommRingCat.{0} ⥤ Type where
  obj A := b.D.obj A × A
  map f := TypeCat.ofHom fun x => (b.D.map f x.1, f.hom x.2)
  map_id A := by
    ext x
    · exact ConcreteCategory.congr_hom (b.D.map_id A) x.1
    · rfl
  map_comp f g := by
    ext x
    · exact ConcreteCategory.congr_hom (b.D.map_comp f g) x.1
    · rfl

private def prC (b : Act) : Act where
  D := prD b
  G := b.G
  smul A g x := (b.smul A g x.1, x.2)
  one_smul A x := Prod.ext (b.one_smul A x.1) rfl
  mul_smul A g h x := Prod.ext (b.mul_smul A g h x.1) rfl
  nat f g x := Prod.ext (b.nat f g x.1) rfl

private def prFst (b : Act) : Act.Hom (prC b) b where
  d := { app := fun A => TypeCat.ofHom fun x => x.1, naturality := fun _ _ _ => rfl }
  g := 𝟙 _
  eq _ _ _ := rfl

private def prSnd (b : Act) : Act.Hom (prC b) affC where
  d := { app := fun A => TypeCat.ofHom fun x => x.2, naturality := fun _ _ _ => rfl }
  g := { app := fun A => GrpCat.ofHom 1, naturality := fun _ _ _ => rfl }
  eq _ _ _ := rfl

private def prLift {a b : Act} (φ : Act.Hom a b) (r : ∀ A : CommRingCat.{0}, a.D.obj A → A)
    (hn : ∀ {A B : CommRingCat.{0}} (f : A ⟶ B) (x : a.D.obj A), r B (a.D.map f x) = f.hom (r A x))
    (hs : ∀ (A : CommRingCat.{0}) (u : a.G.obj A) (x : a.D.obj A), r A (a.smul A u x) = r A x) : Act.Hom a (prC b) where
  d :=
    { app := fun A => TypeCat.ofHom fun x => (φ.d.app A x, r A x)
      naturality := fun A B f => by
        ext x
        have h := ConcreteCategory.congr_hom (φ.d.naturality f) x
        exact Prod.ext h (hn f x) }
  g := φ.g
  eq A u x := Prod.ext (φ.eq A u x) (hs A u x)

private theorem inv_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {t : A} (h : IsUnit t) :
    Ring.inverse (f t) = f (Ring.inverse t) := by
  have a1 : f t * f (Ring.inverse t) = 1 := by rw [← map_mul, Ring.mul_inverse_cancel t h, map_one]
  have a2 : Ring.inverse (f t) * f t = 1 := Ring.inverse_mul_cancel _ (h.map f)
  exact left_inv_eq_right_inv a2 a1

private abbrev cC (N : ℕ) : Act := (BC N).sub ((Q1 N).comap (βC N))

private abbrev piC (N : ℕ) : Act.Hom (cC N) (XC N) := (incl ((Q1 N).comap (βC N))).comp (pC N)

private abbrev aC (N : ℕ) (Q : Pred (XC N)) : Act := (cC N).sub (Q.comap (piC N))

section
variable {N : ℕ} {Q : Pred (XC N)} {A : CommRingCat.{0}}

private def vOf (x : (aC N Q).D.obj A) : Um N A := x.1.1.1
private def sOf (x : (aC N Q).D.obj A) : A := x.1.1.2.1 0
private def tOf (x : (aC N Q).D.obj A) : A := x.1.1.2.1 1

private theorem t_unit (x : (aC N Q).D.obj A) : IsUnit (tOf x) := by
  have h : IsUnit ((Um.join x.1.1).1 (Fin.last N)) := x.1.2
  simpa [Um.join, tOf] using h

private theorem v_unit {i : Fin N} (hQ : Q.Le (unitAt i)) (x : (aC N Q).D.obj A) : IsUnit ((vOf x).1 i) :=
  hQ A _ x.2

private def rOf (i : Fin N) (x : (aC N Q).D.obj A) : A := sOf x * (vOf x).1 i * Ring.inverse (tOf x)

private theorem r_nat (i : Fin N) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : (aC N Q).D.obj A) :
    rOf i ((aC N Q).D.map f x) = f.hom (rOf i x) := by
  have hs : sOf ((aC N Q).D.map f x) = f.hom (sOf x) := rfl
  have hv : (vOf ((aC N Q).D.map f x)).1 i = f.hom ((vOf x).1 i) := rfl
  have ht : tOf ((aC N Q).D.map f x) = f.hom (tOf x) := rfl
  simp only [rOf, hs, hv, ht, map_mul, inv_map f.hom (t_unit x)]

private theorem r_smul (i : Fin N) (u : (aC N Q).G.obj A) (x : (aC N Q).D.obj A) :
    rOf i ((aC N Q).smul A u x) = rOf i x := by
  let l : Aˣ := (show Aˣ × Aˣ from u).1
  let m : Aˣ := (show Aˣ × Aˣ from u).2
  have hs : sOf ((aC N Q).smul A u x) = ((m : A) * ((l⁻¹ : Aˣ) : A)) * sOf x := rfl
  have hv : (vOf ((aC N Q).smul A u x)).1 i = (l : A) * (vOf x).1 i := rfl
  have ht : tOf ((aC N Q).smul A u x) = (m : A) * tOf x := rfl
  have hw : Ring.inverse ((m : A) * tOf x) * ((m : A) * tOf x) = 1 :=
    Ring.inverse_mul_cancel _ (m.isUnit.mul (t_unit x))
  have ht1 : tOf x * Ring.inverse (tOf x) = 1 := Ring.mul_inverse_cancel _ (t_unit x)
  have hl : (l : A) * ((l⁻¹ : Aˣ) : A) = 1 := by simp
  simp only [rOf, hs, hv, ht]
  linear_combination ((m : A) * sOf x * (vOf x).1 i * Ring.inverse ((m : A) * tOf x)) * hl +
    (sOf x * (vOf x).1 i * Ring.inverse (tOf x)) * hw -
    (sOf x * (vOf x).1 i * (m : A) * Ring.inverse ((m : A) * tOf x)) * ht1

private theorem s_of_r {i : Fin N} (hQ : Q.Le (unitAt i)) (x : (aC N Q).D.obj A) :
    sOf x = rOf i x * tOf x * Ring.inverse ((vOf x).1 i) := by
  have ht1 : tOf x * Ring.inverse (tOf x) = 1 := Ring.mul_inverse_cancel _ (t_unit x)
  have hv1 : (vOf x).1 i * Ring.inverse ((vOf x).1 i) = 1 := Ring.mul_inverse_cancel _ (v_unit hQ x)
  simp only [rOf]
  linear_combination (-(sOf x * tOf x * Ring.inverse (tOf x))) * hv1 - sOf x * ht1

private def tVec (x : (aC N Q).D.obj A) : Um 1 A :=
  ⟨fun _ => tOf x, Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) (t_unit x)⟩

end

private theorem unimodularRow_one_isUnit {A : Type} [CommRing A] (w : Um 1 A) : IsUnit (w.1 0) := by
  have h := w.2
  rw [Set.range_unique] at h
  exact Ideal.span_singleton_eq_top.1 h

private theorem join_last {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) :
    (Um.join x).1 (Fin.last N) = x.2.1 1 := by
  simp [Um.join]

private def tHom (N : ℕ) (Q : Pred (XC N)) : Act.Hom (aC N Q) (XC 1) where
  d :=
    { app := fun A => TypeCat.ofHom tVec
      naturality := fun A B f => by
        ext x
        exact Subtype.ext (funext fun _ => rfl) }
  g := (βC N).g
  eq A u x := Subtype.ext (funext fun _ => rfl)

private def rHom {N : ℕ} (Q : Pred (XC N)) (i : Fin N) : Act.Hom (aC N Q) (prC ((XC N).sub Q)) :=
  prLift ((piC N).sub Q) (fun A x => rOf i x) (fun f x => r_nat i f x) (fun A u x => r_smul i u x)

private def mkA {N : ℕ} {Q : Pred (XC N)} (i : Fin N) {A : CommRingCat.{0}} (v : Um N A) (hv : Q.P A v) (r : A) (w : Um 1 A) :
    (aC N Q).D.obj A :=
  Subtype.mk (Subtype.mk
    ((v, ⟨![r * w.1 0 * Ring.inverse (v.1 i), w.1 0],
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨1, rfl⟩) (unimodularRow_one_isUnit w)⟩) : Um N A × Um 2 A)
    (by
      change IsUnit ((Um.join _).1 (Fin.last N))
      rw [join_last]
      exact unimodularRow_one_isUnit w)) hv

private theorem d_bij {N : ℕ} {Q : Pred (XC N)} {i : Fin N} (hQ : Q.Le (unitAt i)) (A : CommRingCat.{0}) :
    Function.Bijective (fun x : (aC N Q).D.obj A =>
      (((rHom Q i).d.app A x, (tHom N Q).d.app A x) : (prC ((XC N).sub Q)).D.obj A × (XC 1).D.obj A)) := by
  constructor
  · intro x y h
    have h1 : vOf x = vOf y := congrArg (fun p : (prC ((XC N).sub Q)).D.obj A × (XC 1).D.obj A => (show Um N A from (show ((XC N).sub Q).D.obj A × A from p.1).1.1)) h
    have h2 : rOf i x = rOf i y := congrArg (fun p : (prC ((XC N).sub Q)).D.obj A × (XC 1).D.obj A => (show ((XC N).sub Q).D.obj A × A from p.1).2) h
    have h3 : tOf x = tOf y := congrArg (fun p : (prC ((XC N).sub Q)).D.obj A × (XC 1).D.obj A => (show Um 1 A from p.2).1 0) h
    have h4 : sOf x = sOf y := by
      rw [s_of_r hQ x, s_of_r hQ y, h1, h2, h3]
    refine Subtype.ext (Subtype.ext (Prod.ext h1 (Subtype.ext (funext fun j => ?_))))
    fin_cases j
    · exact h4
    · exact h3
  · intro y
    let v : Um N A := (show ((XC N).sub Q).D.obj A × A from y.1).1.1
    have hv : Q.P A v := (show ((XC N).sub Q).D.obj A × A from y.1).1.2
    let r : A := (show ((XC N).sub Q).D.obj A × A from y.1).2
    let w : Um 1 A := y.2
    have hvu : IsUnit (v.1 i) := hQ A v hv
    have hv1 : v.1 i * Ring.inverse (v.1 i) = 1 := Ring.mul_inverse_cancel _ hvu
    have ht1 : w.1 0 * Ring.inverse (w.1 0) = 1 := Ring.mul_inverse_cancel _ (unimodularRow_one_isUnit w)
    refine ⟨mkA i v hv r w, Prod.ext (Prod.ext (Subtype.ext rfl) ?_) (Subtype.ext (funext fun j => ?_))⟩
    · change r * w.1 0 * Ring.inverse (v.1 i) * v.1 i * Ring.inverse (w.1 0) = r
      linear_combination (r * w.1 0 * Ring.inverse (w.1 0)) * hv1 + r * ht1
    · rw [Subsingleton.elim j 0]
      rfl

private theorem g_bij {N : ℕ} (Q : Pred (XC N)) (i : Fin N) (A : CommRingCat.{0}) :
    Function.Bijective (fun g : (aC N Q).G.obj A =>
      (((rHom Q i).g.app A g, (tHom N Q).g.app A g) : (prC ((XC N).sub Q)).G.obj A × (XC 1).G.obj A)) := by
  constructor
  · intro g h e
    exact Prod.ext (congrArg Prod.fst e) (congrArg Prod.snd e)
  · intro y
    exact ⟨(show Aˣ × Aˣ from y), rfl⟩

private theorem pr_d_bij (b : Act) (A : CommRingCat.{0}) :
    Function.Bijective (fun x : (prC b).D.obj A => (((prFst b).d.app A x, (prSnd b).d.app A x) : b.D.obj A × affC.D.obj A)) :=
  ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

private theorem pr_g_bij (b : Act) (A : CommRingCat.{0}) :
    Function.Bijective (fun g : (prC b).G.obj A => (((prFst b).g.app A g, (prSnd b).g.app A g) : b.G.obj A × affC.G.obj A)) :=
  ⟨fun _ _ h => congrArg Prod.fst h, fun y => ⟨y.1, rfl⟩⟩

private theorem hom_ext' {a b : Act} {φ ψ : Act.Hom a b} (h1 : φ.d = ψ.d) (h2 : φ.g = ψ.g) : φ = ψ := by
  cases φ
  cases ψ
  cases h1
  cases h2
  rfl

private theorem comp_cat {a b c : Act} (φ : Act.Hom a b) (ψ : Act.Hom b c) : (φ.comp ψ).cat = φ.cat ≫ ψ.cat :=
  NatTrans.ext (funext fun _ => Cat.Hom.ext (CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)))

private theorem spc_comp {a b c : Act} (φ : Act.Hom a b) (ψ : Act.Hom b c) :
    spcMap (φ.comp ψ) = spcMap φ ≫ spcMap ψ := by
  change ofCatMap (φ.comp ψ).cat = ofCatMap φ.cat ≫ ofCatMap ψ.cat
  rw [comp_cat]
  simp only [ofCatMap, Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
  exact Functor.map_comp _ _ _

private theorem sp_comp (E : Spc) {a b c : Act} (φ : Act.Hom a b) (ψ : Act.Hom b c) :
    Sp.map E (φ.comp ψ) = Sp.map E φ ≫ Sp.map E ψ := by
  rw [Sp.map, spc_comp]
  rfl

private theorem rHom_fst {N : ℕ} (Q : Pred (XC N)) (i : Fin N) :
    (rHom Q i).comp (prFst ((XC N).sub Q)) = (piC N).sub Q :=
  hom_ext' rfl (Category.comp_id _)

private theorem eqv_comp {R : Type} [CommRing R] {X Y Z : Spc} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Shv R) (hf : Eqv R f F)
    (hg : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n) := funext fun x => pull_comp R f g F n x
  rw [h]
  exact (hf n).comp (hg n)

private theorem eqv_iso {R : Type} [CommRing R] {X Y : Spc} (f : X ⟶ Y) [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
    fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

private theorem lh_one {q : ℕ} {X E : Spc} (π : X ⟶ E) (d e : Fin 1 → ℤ) (c : ∀ j, Ht q X (d j) (e j))
    (hd : ∀ j, 0 = d j) (he : ∀ j, 0 = e j) (hc : ∀ j, c j = (one q X).cast (hd j) (he j)) (h : LH q π d e c) :
    LH q π (fun _ : Fin 1 => (0 : ℤ)) (fun _ : Fin 1 => (0 : ℤ)) (fun _ => one q X) := by
  obtain rfl : d = fun _ => 0 := funext fun j => (hd j).symm
  obtain rfl : e = fun _ => 0 := funext fun j => (he j).symm
  obtain rfl : c = fun _ => one q X := funext fun j => hc j
  exact h

private theorem eqv_fst (q : ℕ) [NeZero q] (S : Spc) (hS : Inv q S) (i : ℤ) : Eqv _ (Sp.fst S (XC 1)) (tw q i) := by
  have h : Pbf q S 1 := (UpperTheory.projBundleFormula_iff_pglForm q S 1 hS).1 (UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q S hS)
  have hX : Inv q (Sp S (XC 1)) := fun U ⟨x⟩ => hS U ⟨x.1⟩
  refine (UpperTheory.lerayHirsch_one_iff_twist_equiv q _ hX).1 (lh_one _ _ _ _ (fun j => ?_) (fun j => ?_) (fun j => ?_) h) i
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl

private theorem eqv_main (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (i : Fin N) (Q : Pred (XC N)) (hQ : Q.Le (unitAt i))
    (hE : Inv q E) (j : ℤ) : Eqv _ (Sp.map E ((piC N).sub Q)) (tw q j) := by
  have hS : Inv q (Sp E ((XC N).sub Q)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hS1 : Inv q (Sp E (prC ((XC N).sub Q))) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  haveI i1 : IsIso (Sp.pair E (rHom Q i) (tHom N Q)) := UpperTheory.isIso_stackProductPair_of_bijective E _ _ (d_bij hQ) (g_bij Q i)
  haveI i2 : IsIso (Sp.pair E (prFst ((XC N).sub Q)) (prSnd ((XC N).sub Q))) :=
    UpperTheory.isIso_stackProductPair_of_bijective E _ _ (pr_d_bij _) (pr_g_bij _)
  have e1 : Sp.map E (rHom Q i) = Sp.pair E (rHom Q i) (tHom N Q) ≫ Sp.fst (Sp E (prC ((XC N).sub Q))) (XC 1) := rfl
  have e2 : Sp.map E (prFst ((XC N).sub Q)) =
      Sp.pair E (prFst ((XC N).sub Q)) (prSnd ((XC N).sub Q)) ≫ Sp.fst (Sp E ((XC N).sub Q)) affC := rfl
  rw [← rHom_fst Q i, sp_comp, e1, e2]
  exact eqv_comp _ _ _ (eqv_comp _ _ _ (eqv_iso _ _) (eqv_fst q _ hS1 j))
    (eqv_comp _ _ _ (eqv_iso _ _) (UpperTheory.affineLineAction_fst_twistEquiv q _ j hS))

end UpperTheory.ProjectiveLineCharts

end

open UpperTheory.ProjectiveLineCharts in
theorem UpperTheory.leraHirsch_unit_on_blowupChart :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → Inv q E →
        LHQ q E ((incl ((Q1 N).comap (βC N))).comp (pC N)) (fun _ : Fin 1 => (0 : ℤ)) (fun _ : Fin 1 => (0 : ℤ)) (fun _ => one q _) Q := by
  intro q _ N E i Q hQ hE
  have hc : Inv q (Sp E ((BC N).sub ((Q1 N).comap (βC N)))) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have ha : Inv q (Sp E (((BC N).sub ((Q1 N).comap (βC N))).sub (Q.comap ((incl ((Q1 N).comap (βC N))).comp (pC N))))) :=
    fun U ⟨x⟩ => hE U ⟨x.1⟩
  have h := (UpperTheory.lerayHirsch_one_iff_twist_equiv q (Sp.map E (((incl ((Q1 N).comap (βC N))).comp (pC N)).sub Q)) ha).2
    (fun j => eqv_main q N E i Q hQ hE j)
  have key : pull _ (Sp.map E (incl (Q.comap ((incl ((Q1 N).comap (βC N))).comp (pC N))))) _ _ (one q _) = one q _ :=
    (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.1 _ hc
  unfold LHQ
  simp only [key]
  exact h
