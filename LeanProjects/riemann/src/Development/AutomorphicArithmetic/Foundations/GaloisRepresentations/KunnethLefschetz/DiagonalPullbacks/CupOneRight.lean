import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.EtaleCohomology.EtaleTrace.LRingPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.PUntw

open LateralTheory.EtaleTrace.LRingPf

private theorem inv_sch {q : ℕ} {X : Scheme.{0}} (hq : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U ⟨f⟩
  have h := hq.map (Scheme.Hom.appTop f).hom
  simpa using h

private theorem swap0 (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Spc} {m d n i t s w : ℤ}
    (a : Ht q E m i) (c : Ht q E d t) (ρ : Ht q E 0 s)
    (hn : m + (d + 0) = n) (hi : i + (t + s) = w) (hn' : m + 0 + d = n) (hi' : i + s + t = w) :
    Ht.cast hn hi (cup q a (cup q c ρ)) = Ht.cast hn' hi' (cup q (cup q a ρ) c) := by
  have hc : cup q c ρ = Ht.cast (by ring) (by ring) (cup q ρ c) := by
    rw [(h6 q E).2.2 c ρ]
    simp
  have hA : cup q (cup q a ρ) c = Ht.cast (by ring) (by ring) (cup q a (cup q ρ c)) :=
    (h6 q E).2.1 a ρ c
  rw [hc, cup_cast_right, LRingPf.cast_cast, hA, LRingPf.cast_cast]

private theorem cup_one_right (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Spc} (hE : Inv q E) {m t : ℤ}
    (a : Ht q E m t) (hn : m + 0 = m) (ht : t + 0 = t) : Ht.cast hn ht (cup q a (one q E)) = a := by
  have hc : cup q a (one q E) = Ht.cast (by ring) (by ring) (cup q (one q E) a) := by
    rw [(h6 q E).2.2 a (one q E)]
    simp
  have hu : cup q (one q E) a = Ht.cast (by ring) (by ring) a := (h6 q E).1 hE a
  rw [hc, hu, LRingPf.cast_cast, LRingPf.cast_cast]
  rfl

private theorem root_idx {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) {i j : ℤ} (h : i = j) :
    rootClass j ζ = Ht.cast rfl h (rootClass i ζ) := by
  subst h; rfl

private theorem two_roots (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {X : Scheme.{0}} (hE : Inv q (sch.obj X))
    (ζ : Prim q Γ(X, ⊤)) {m t i j : ℤ} (a : Ht q (sch.obj X) m t) (hij : i + j = 0)
    (hn : m + 0 + 0 = m) (ht : t + i + j = t) :
    Ht.cast hn ht (cup q (cup q a (rootClass i ζ)) (rootClass j ζ)) = a := by
  have hA : cup q (cup q a (rootClass i ζ)) (rootClass j ζ) =
      Ht.cast (by ring) (by ring) (cup q a (cup q (rootClass i ζ) (rootClass j ζ))) :=
    (h6 q (sch.obj X)).2.1 a _ _
  rw [hA, ((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 X ζ i j).1, root_idx ζ hij.symm, ((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 X ζ 0 0).2,
    LRingPf.cast_cast, LRingPf.cast_cast, cup_cast_right, LRingPf.cast_cast]
  exact cup_one_right h6 hE a (by ring) (by ring)

private theorem bij_root (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {X : Scheme.{0}} (hE : Inv q (sch.obj X))
    (ζ : Prim q Γ(X, ⊤)) (m w : ℤ) :
    Function.Bijective fun a : Ht q (sch.obj X) m 0 =>
      Ht.cast (add_zero m) (zero_add w) (cup q a (rootClass w ζ)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun b => Ht.cast (add_zero m) (add_neg_cancel w) (cup q b (rootClass (-w) ζ)), ?_, ?_⟩
  · intro a
    simp only
    rw [cup_cast_left, LRingPf.cast_cast]
    exact two_roots h6 hE ζ a (add_neg_cancel w) (by ring) (by ring)
  · intro b
    simp only
    rw [cup_cast_left, LRingPf.cast_cast]
    exact two_roots h6 hE ζ b (neg_add_cancel w) (by ring) (by ring)

private theorem term (hI : In) (hR : RootNat) (hP : PowRoot) {q : ℕ} [NeZero q] {E Z : Scheme.{0}} (r : E ⟶ Z)
    (ζ : Prim q Γ(Z, ⊤)) (x : Ht q (sch.obj E) 2 1) (n : ℤ) (j : ℕ) (a : Ht q (sch.obj Z) (n - 2 * (j : ℤ)) 0) :
    cup0 q (sub_add_cancel n _) (pull _ (sch.map r) _ _ a)
        (pow0 q (untw q x (rootClass (-1) (ζ.map r.appTop.hom))) j) =
      ((cup q (pull _ (sch.map r) _ _ (Ht.cast (add_zero _) (zero_add _) (cup q a (rootClass ((0 : ℤ) - (j : ℤ)) ζ))))
        (cpow q x j)).cast (by ring) (by ring) : Ht q _ n 0) := by
  have h6 := hI.a6ring
  have hN := (hI.a6nat q).1 (sch.map r) a (rootClass ((0 : ℤ) - (j : ℤ)) ζ)
  rw [hP hI q (ζ.map r.appTop.hom) x j]
  simp only [cup0]
  rw [cup_cast_right, LRingPf.cast_cast, pull_cast, hN, hR q _ r ζ, cup_cast_left, LRingPf.cast_cast,
    root_idx (ζ.map r.appTop.hom) (show (0 : ℤ) - j = -j by ring), cup_cast_right, cup_cast_right,
    LRingPf.cast_cast]
  exact swap0 h6 _ _ _ _ _ _ _

end UpperTheory.Gal.KunnethLefschetz.Di.PUntw

open UpperTheory.Gal.KunnethLefschetz.Di.PUntw in
theorem UpperTheory.Gal.KunnethLefschetz.Di.untw_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.Untw := by
  intro hI hR hP q _ N E Z r ζ x hT n
  have h6 := hI.a6ring
  have hE : Inv q (sch.obj Z) := inv_sch ζ.2.1
  let Φ : ((j : Fin N) → Ht q (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) 0) →
      ((j : Fin N) → Ht q (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) ((0 : ℤ) - ((j : ℕ) : ℤ))) :=
    fun a j => Ht.cast (add_zero _) (zero_add _) (cup q (a j) (rootClass ((0 : ℤ) - ((j : ℕ) : ℤ)) ζ))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro a b h
      funext j
      exact (bij_root h6 hE ζ _ _).1 (congrFun h j)
    · intro c
      choose a ha using fun j : Fin N => (bij_root h6 hE ζ _ ((0 : ℤ) - ((j : ℕ) : ℤ))).2 (c j)
      exact ⟨a, funext ha⟩
  have hc := (hT n 0).comp hΦ
  convert hc using 1
  funext a
  simp only [Function.comp, Φ]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact term hI hR hP r ζ x n j (a j)
