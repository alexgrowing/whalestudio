import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem UpperTheory.Gal.Ord.eq_one_of_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {y' : T.left ⟶ S}
    (hy : T.hom ≫ f = y') (x₀ : Over.mk y' ⟶ G) (hx : x₀.left = (1 : T ⟶ G').left ≫ φ) : x₀ = 1 := by
  subst hy
  have h2 := h.2 T 1 1 x₀ x₀ hx hx
  have hsq : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, _root_.mul_one, hx]
  exact mul_eq_left.mp hsq

private theorem UpperTheory.Gal.Ord.one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {y' : T.left ⟶ S}
    (hy : T.hom ≫ f = y') : (1 : Over.mk y' ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk y').hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    exact hy
  have e := eq_one_of_left h T hy (Over.homMk ((1 : T ⟶ G').left ≫ φ) hw) rfl
  rw [← e]
  rfl

private theorem UpperTheory.Gal.Ord.killedBy_iff {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}
    (m : ObjMap o' o f) (v : Ideal (𝓞 D.F)) (T : Over S') {y' : T.left ⟶ S} (hy : T.hom ≫ f = y')
    (x : T ⟶ o'.A) (x₀ : Over.mk y' ⟶ o.A) (hx : x₀.left = x.left ≫ m.φ) :
    KilledBy o v x₀ ↔ KilledBy o' v x := by
  have key : ∀ c : D.O, (x₀ ≫ o.act.act c).left = (x ≫ o'.act.act c).left ≫ m.φ := by
    intro c
    rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, m.act c]
  unfold KilledBy
  constructor
  · intro H a ha
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [← key, H a ha]
      exact one_left m.cart T hy
    · simp only [Over.w]
  · intro H a ha
    apply eq_one_of_left m.cart T hy
    rw [key, H a ha]

theorem UpperTheory.Gal.Ord.ordPull :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F))
      (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (s₀ : Sp k ⟶ Sp R) (o₀ : Obj b N s₀), ObjMap o₀ o y → IsWOrd o₀ w (𝟙 (Sp k)) → IsWOrd o w y := by
  intro p _ D R _ b N S s o w k _ _ y s₀ o₀ m h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rw [← h4]
  have hy : (Over.mk (𝟙 (Sp k))).hom ≫ y = y := by simp
  apply Nat.card_congr
  exact
    { toFun := fun g =>
        ⟨Over.homMk (m.cart.1.lift g.1.left (𝟙 _) (by simp)) (by rw [IsPullback.lift_snd]; rfl),
          (killedBy_iff m w _ hy _ g.1 (m.cart.1.lift_fst _ _ _).symm).mp g.2⟩
      invFun := fun g =>
        ⟨Over.homMk (g.1.left ≫ m.φ) (by rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; simp),
          (killedBy_iff m w _ hy g.1 _ rfl).mpr g.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        simp
      right_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        apply m.cart.1.hom_ext
        · simp
        · simp }
