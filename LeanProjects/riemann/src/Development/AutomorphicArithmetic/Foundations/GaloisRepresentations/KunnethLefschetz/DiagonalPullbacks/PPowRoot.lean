import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.EtaleCohomology.EtaleTrace.LRingPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf

namespace UpperTheory.Gal.KunnethLefschetz.Di

private theorem inv_root {q : ℕ} {E : Scheme.{0}} (ζ : Prim q Γ(E, ⊤)) : Inv q (sch.obj E) := by
  intro U hU
  obtain ⟨y⟩ := hU
  let y' : U ⟶ E := y
  simpa using ζ.2.1.map y'.appTop.hom

private theorem cast_eq_iff {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) (y : Ht q E n' i') :
    Ht.cast h1 h2 x = y ↔ x = Ht.cast h1.symm h2.symm y := by
  subst h1 h2; rfl

private theorem rootClass_cast {q : ℕ} {E : Scheme.{0}} (ζ : Prim q Γ(E, ⊤)) {i i' : ℤ} (h : i = i') (h0 : (0 : ℤ) = 0) :
    rootClass i' ζ = Ht.cast h0 h (rootClass i ζ) := by
  subst h; rfl

private theorem swap0 (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Spc} {m k s : ℤ} (r : Ht q E 0 s) (b : Ht q E m k) :
    cup q r b = Ht.cast (by ring) (by ring) (cup q b r) := by
  rw [(h6 q E).2.2 r b]
  simp

private theorem four (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Spc} {n m i k s t : ℤ} (a : Ht q E n i) (r : Ht q E 0 s)
    (b : Ht q E m k) (c : Ht q E 0 t) :
    cup q (cup q a r) (cup q b c) = Ht.cast (by ring) (by ring) (cup q (cup q a b) (cup q r c)) := by
  have e1 : cup q r (cup q b c) = Ht.cast (by ring) (by ring) (cup q b (cup q r c)) := by
    have e2 := (cast_eq_iff _ _ _ _).1 ((h6 q E).2.1 r b c).symm
    rw [e2, swap0 h6 r b, cup_cast_left, (h6 q E).2.1 b r c, LRingPf.cast_cast, LRingPf.cast_cast]
  rw [(h6 q E).2.1 a r (cup q b c), e1, cup_cast_right, LRingPf.cast_cast, (h6 q E).2.1 a b (cup q r c),
    LRingPf.cast_cast]

private theorem base (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Scheme.{0}} (ζ : Prim q Γ(E, ⊤)) {n i : ℤ} (hn : 0 = n) (hi : 0 = i)
    (h0 : (0 : ℤ) = 0) (h1 : n + 0 = n) (h2 : i + -i = 0) :
    Ht.cast hn h0 (one q (sch.obj E)) = Ht.cast h1 h2 (cup q (Ht.cast hn hi (one q (sch.obj E))) (rootClass (-i) ζ)) := by
  subst hn hi
  have hr : rootClass (-(0 : ℤ)) ζ = Ht.cast h0 (neg_zero.symm : (0 : ℤ) = -0) (one q (sch.obj E)) := by
    rw [rootClass_cast ζ (neg_zero.symm : (0 : ℤ) = -0) h0, ((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 E ζ 0 0).2]
  rw [hr, cup_cast_left, cup_cast_right, LRingPf.cast_cast, LRingPf.cast_cast, (h6 q _).1 (inv_root ζ) (one q (sch.obj E)),
    LRingPf.cast_cast]

theorem powRoot_holds : PowRoot := by
  intro hI q _ E ζ x j
  have h6 := hI.a6ring
  induction j with
  | zero =>
    exact base h6 ζ (n := 2 * ((0 : ℕ) : ℤ)) (i := ((0 : ℕ) : ℤ)) (by simp) (by simp) (Eq.refl 0) _ _
  | succ j ih =>
    have e : pow0 q (untw q x (rootClass (-1) ζ)) (j + 1) =
      cup0 q (by push_cast; ring) (pow0 q (untw q x (rootClass (-1) ζ)) j) (untw q x (rootClass (-1) ζ)) := rfl
    rw [e, ih]
    unfold cup0 untw
    rw [cup_cast_left, cup_cast_right, LRingPf.cast_cast, LRingPf.cast_cast, four h6, ((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 E ζ _ _).1,
      cup_cast_right, LRingPf.cast_cast, cpow_succ, cup_cast_left,
      rootClass_cast ζ (show -(j : ℤ) + -1 = -((j + 1 : ℕ) : ℤ) by push_cast; ring) (Eq.refl 0), cup_cast_right,
      LRingPf.cast_cast, LRingPf.cast_cast, LRingPf.cast_cast]

end UpperTheory.Gal.KunnethLefschetz.Di
