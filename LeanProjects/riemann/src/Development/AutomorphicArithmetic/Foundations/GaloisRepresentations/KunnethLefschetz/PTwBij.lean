import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LRingPf
import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem inv_of_unit {q : ℕ} {X : Scheme.{0}} (hl : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U hU
  obtain ⟨y⟩ := hU
  let y' : U ⟶ X := y
  simpa using hl.map y'.appTop.hom

private theorem cancel_lemma {q : ℕ} {E : Spc} {n i : ℤ} (h1 : n = n) (h2 : i = i) (x : Ht q E n i) :
    Ht.cast h1 h2 x = x := rfl

private theorem eq_of_mul_mul_eq_of_det_ne_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (y : Ht q E n' i') (h : Ht.cast h1 h2 x = y) : x = Ht.cast h1.symm h2.symm y := by
  subst h
  rw [LRingPf.cast_cast, cancel_lemma]

private theorem cancel {q : ℕ} [NeZero q] (h6 : DivisorRingCompatibility) {E : Spc} (hi : Inv q E) {i i' : ℤ} (hs : i + i' = 0)
    (a : Ht q E 0 i) (b : Ht q E 0 i') (hab : (cup q a b).cast (add_zero 0) hs = one q E) {n j w : ℤ}
    (h1 : i' + j = w) (h2 : i + w = j) (c : Ht q E n j) :
    (cup q a ((cup q b c).cast (zero_add n) h1)).cast (zero_add n) h2 = c := by
  obtain ⟨hone, hassoc, -⟩ := h6 q E
  have e1 := hassoc a b c
  rw [eq_of_mul_mul_eq_of_det_ne_zero _ _ _ _ hab, cup_cast_left, hone hi, LRingPf.cast_cast] at e1
  have e3 := eq_of_mul_mul_eq_of_det_ne_zero _ _ _ _ e1.symm
  rw [cup_cast_right, LRingPf.cast_cast, e3, LRingPf.cast_cast, LRingPf.cast_cast, cancel_lemma]

private theorem swap {q : ℕ} [NeZero q] (h6 : DivisorRingCompatibility) {E : Spc} {i i' : ℤ} (hs : i + i' = 0) (hs' : i' + i = 0)
    (a : Ht q E 0 i) (b : Ht q E 0 i') (hab : (cup q a b).cast (add_zero 0) hs = one q E) :
    (cup q b a).cast (add_zero 0) hs' = one q E := by
  rw [(h6 q E).2.2 b a, cast_usmul, LRingPf.cast_cast, hab]
  simp

private theorem bij_of (hI : In) {k : Type} [Field k] {q : ℕ} [NeZero q] (hq : IsUnit (q : k)) {i i' : ℤ}
    (hs : i + i' = 0) (u : Ht q (sch.obj (S k)) 0 i) (v : Ht q (sch.obj (S k)) 0 i')
    (huv : (cup q u v).cast (add_zero 0) hs = one q (sch.obj (S k))) {X : Scheme.{0}} (p : X ⟶ S k) (n j w : ℤ)
    (hw : i + j = w) : Function.Bijective (twMul q p hw u n) := by
  have hX : Inv q (sch.obj X) := inv_of_unit (LPdCut.unit_of p hq)
  have hS : Inv q (sch.obj (S k)) := inv_of_unit (LPdCut.unit_of (𝟙 (S k)) hq)
  have hUV : (cup q (pull _ (sch.map p) _ 0 u) (pull _ (sch.map p) _ 0 v)).cast (add_zero 0) hs = one q (sch.obj X) := by
    rw [← (hI.a6nat q).2.1 (sch.map p) hS, ← huv, pull_cast, (hI.a6nat q).1]
  have hs' : i' + i = 0 := by omega
  have hVU := swap hI.a6ring hs hs' _ _ hUV
  have h : i' + w = j := by omega
  refine Function.bijective_iff_has_inverse.2 ⟨twMul q p h v n, fun c => ?_, fun c => ?_⟩
  · exact cancel hI.a6ring hX hs' _ _ hVU hw h c
  · exact cancel hI.a6ring hX hs _ _ hUV h hw c

theorem twBij_holds : TwBij := by
  unfold TwBij
  intro hI k _ q _ hq i u v huv X p n j w
  have hvu := swap hI.a6ring (add_neg_cancel i) (neg_add_cancel i) u v huv
  exact ⟨fun hw => bij_of hI hq (neg_add_cancel i) v u hvu p n j w hw,
    fun hw => bij_of hI hq (add_neg_cancel i) u v huv p n j w hw⟩

end UpperTheory.Gal.KunnethLefschetz
