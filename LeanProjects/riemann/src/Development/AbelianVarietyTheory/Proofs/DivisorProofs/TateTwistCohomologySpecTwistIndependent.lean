import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHoldStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.Untwist

theorem res_X_isZero {R : Type} [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (y : Sec F U) : y = 0 := by
  have h := congrArg (fun φ : F ⟶ F => Sec.map φ y) (hF.eq_of_src (𝟙 F) 0)
  exact h

theorem sec_res_neg {R : Type} [CommRing R] (F : Shv R) {n : ℤ} (hn : n < 0) {U : Scheme.{0}} (y z : Sec ((res R F).X n) U) :
    y = z := (sec_eq_zero (res_X_isZero F n hn) y).trans (sec_eq_zero (res_X_isZero F n hn) z).symm

theorem cocycle_ext_zero {R : Type} [CommRing R] {X : Scheme.{0}} {F : Shv R}
    (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0)
    (h : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = ev β.1 0 0 (by simp) U x) : α = β := by
  refine Cocycle.ext (CupSpec.ev_ext _ _ fun p s hs U x => ?_)
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using hs.symm
    exact h U x
  | succ p => exact sec_res_neg F (by omega) _ _

theorem cup_rootClass {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (a b : ℤ) :
    cup q (rootClass a ζ) (rootClass b ζ) = (rootClass (a + b) ζ : Ht q (sch.obj X) (0 + 0) (a + b)) := by
  obtain ⟨α, hα, hα'⟩ := rootClass_spec a ζ
  obtain ⟨β, hβ, hβ'⟩ := rootClass_spec b ζ
  obtain ⟨γ, hγ, hγ'⟩ := rootClass_spec (a + b) ζ
  rw [← hα, ← hβ, ← hγ]
  refine Pair.cup_spec (twPair q a b) (sch.obj X) rfl α β γ ?_
  intro N w hw U x
  cases N with
  | zero =>
    obtain rfl : w = 0 := by simpa using hw.symm
    rw [Fin.sum_univ_one]
    change ev γ.1 0 0 _ U x = ((0 : ℤ) * 0).negOnePow • (twPair q a b).mul U 0 0 0 rfl (ev α.1 0 0 (by simp) U x) (ev β.1 0 0 (by simp) U x)
    have e1 : ev α.1 0 0 (by simp) U x = _ := hα' U x
    have e2 : ev β.1 0 0 (by simp) U x = _ := hβ' U x
    rw [e1, e2, mul_zero, Int.negOnePow_zero, one_smul]
    refine Eq.trans (hγ' U x) ?_
    change Sec.res (show U ⟶ X from x) _ = (twPair q a b).mul U 0 0 0 rfl (Sec.res (show U ⟶ X from x) _) (Sec.res (show U ⟶ X from x) _)
    rw [ClsSpec.res_resGen, ClsSpec.res_resGen, ClsSpec.res_resGen]
    exact (twPair_spec q a b U _).symm
  | succ N => exact sec_res_neg _ (by omega) _ _

theorem rootClass_zero {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (hX : Inv q (sch.obj X)) :
    rootClass 0 ζ = one q (sch.obj X) := by
  obtain ⟨α, hα, hα'⟩ := rootClass_spec 0 ζ
  obtain ⟨β, hβ, hβ'⟩ := one_spec q (sch.obj X) hX
  rw [← hα, ← hβ]
  refine congrArg CohomologyClass.mk (cocycle_ext_zero α β fun U x => ?_)
  rw [hα', hβ' U x (ζ.map x.appTop.hom), ClsSpec.res_resGen]

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_cast {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h₁ : n = n') (h₂ : i = i') (h₃ : n' = n'') (h₄ : i' = i'') :
    (x.cast h₁ h₂).cast h₃ h₄ = x.cast (h₁.trans h₃) (h₂.trans h₄) := by
  subst h₁; subst h₂; subst h₃; subst h₄; rfl

theorem cast_add {n i n' i' : ℤ} (x y : Ht q E n i) (hn : n = n') (hi : i = i') :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

theorem eq_cast_symm {n i n' i' : ℤ} {x : Ht q E n i} {y : Ht q E n' i'} (hn : n' = n) (hi : i' = i) (h : x = y.cast hn hi) :
    y = x.cast hn.symm hi.symm := by
  subst hn; subst hi; exact h.symm

theorem cup_cast_left {n m i j n' i' : ℤ} (x : Ht q E n i) (b : Ht q E m j) (hn : n = n') (hi : i = i') :
    cup q (x.cast hn hi) b = (cup q x b).cast (congrArg (· + m) hn) (congrArg (· + j) hi) := by
  subst hn; subst hi; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (a : Ht q E n i) (y : Ht q E m j) (hm : m = m') (hj : j = j') :
    cup q a (y.cast hm hj) = (cup q a y).cast (congrArg (n + ·) hm) (congrArg (i + ·) hj) := by
  subst hm; subst hj; rfl

theorem cup_cup_of_unit [NeZero q] (hE : Inv q E) {d e n i : ℤ} (u : Ht q E 0 d) (v : Ht q E 0 e) (hde : (0 : ℤ) = e + d)
    (hvu : cup q v u = (one q E).cast (by simp) hde) (a : Ht q E n i)
    {k : ℤ} (h₁ : 0 + n = n) (h₂ : d + i = k) (h₃ : 0 + n = n) (h₄ : e + k = i) :
    (cup q v ((cup q u a).cast h₁ h₂)).cast h₃ h₄ = a := by
  have hring := GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q E
  have hassoc := eq_cast_symm _ _ (hring.2.1 v u a)
  rw [cup_cast_right, cast_cast, hassoc, cast_cast, hvu, cup_cast_left, cast_cast, hring.1 hE a, cast_cast]
  rfl

end Cast

theorem rootClass_cast {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) {k k' : ℤ} (h : k = k') (hn : (0 : ℤ) = 0 + 0) :
    (rootClass k ζ).cast hn h = (rootClass k' ζ : Ht q (sch.obj X) (0 + 0) k') := by
  subst h; rfl

noncomputable def twistEquiv {q : ℕ} [NeZero q] {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (hX : Inv q (sch.obj X)) (n i j : ℤ) :
    Ht q (sch.obj X) n i ≃+ Ht q (sch.obj X) n j := by
  have key : ∀ d e : ℤ, ∀ hde : (0 : ℤ) = e + d,
      cup q (rootClass e ζ) (rootClass d ζ) = (one q (sch.obj X)).cast (by simp) hde := by
    intro d e hde
    rw [cup_rootClass, ← rootClass_zero ζ hX, rootClass_cast ζ hde]
  exact
    { toFun := fun a => (cup q (rootClass (j - i) ζ) a).cast (zero_add n) (by ring)
      invFun := fun b => (cup q (rootClass (i - j) ζ) b).cast (zero_add n) (by ring)
      left_inv := fun a => cup_cup_of_unit hX _ _ (by ring) (key _ _ (by ring)) a _ _ _ _
      right_inv := fun b => cup_cup_of_unit hX _ _ (by ring) (key _ _ (by ring)) b _ _ _ _
      map_add' := fun a b => by simp only [map_add, cast_add] }

end GlobalTheory.EtC.Untwist

open GlobalTheory.EtC.Untwist in

theorem GlobalTheory.EtC.untwist : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) →
    (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → ∀ n i j : ℤ, Nonempty (Ht q (sp A) n i ≃+ Ht q (sp A) n j) := by
  intro q _ A _ hq ⟨z, hz⟩ n i j
  let φ : A →+* Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hX : Inv q (sp A) := fun U ⟨x⟩ => by
    have h := (hq.map φ).map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom
    simpa only [map_natCast] using h
  exact ⟨twistEquiv (Prim.map φ ⟨z, hq, hz⟩) hX n i j⟩
