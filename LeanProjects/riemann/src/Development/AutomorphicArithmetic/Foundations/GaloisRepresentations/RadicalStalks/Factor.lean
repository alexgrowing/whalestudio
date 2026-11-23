import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueOfBaseEq

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.factor :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p →
      ∀ (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (g : S'' ⟶ S'),
      f ≫ s = s' → g ≫ s' = s'' → ObjMap o' o f → ObjMap o'' o (g ≫ f) → Nonempty (ObjMap o'' o' g) := by
  intro p _ D R _ b N hN hNp S S' S'' s s' s'' o o' o'' f g hf hg m1 m2
  have hw : m2.φ ≫ o.A.hom = (o''.A.hom ≫ g) ≫ f := by
    rw [m2.cart.1.w, Category.assoc]
  let φ' : o''.A.left ⟶ o'.A.left := m1.cart.1.lift m2.φ (o''.A.hom ≫ g) hw
  have h1 : φ' ≫ m1.φ = m2.φ := m1.cart.1.lift_fst _ _ _
  have h2 : φ' ≫ o'.A.hom = o''.A.hom ≫ g := m1.cart.1.lift_snd _ _ _
  let φ₂' : (G2 o''.A).left ⟶ (G2 o'.A).left :=
    pullback.lift (pullback.fst _ _ ≫ φ') (pullback.snd _ _ ≫ φ')
      (by simp only [Category.assoc, h2]; rw [pullback.condition_assoc])
  have sq : Geo.Tor.IsSquare φ' φ₂' := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h3 : φ₂' ≫ m1.φ₂ = m2.φ₂ := by
    apply pullback.hom_ext
    · change φ₂' ≫ m1.φ₂ ≫ Over.Hom.left (fst o.A o.A) = m2.φ₂ ≫ Over.Hom.left (fst o.A o.A)
      rw [m1.sq.1, m2.sq.1, ← Category.assoc, sq.1, Category.assoc, h1]
    · change φ₂' ≫ m1.φ₂ ≫ Over.Hom.left (snd o.A o.A) = m2.φ₂ ≫ Over.Hom.left (snd o.A o.A)
      rw [m1.sq.2, m2.sq.2, ← Category.assoc, sq.2, Category.assoc, h1]
  have cart : IsGrpPullback o''.A o'.A g φ' := by
    refine IsGrpPullback.cancel m1.cart ?_ h2
    rw [h1]
    exact m2.cart
  have pol : LBIso o''.P (o'.P.pull φ₂') := by
    rw [← GlobalTheory.CechPic.cls_eq_iff o''.isLB (pull_isLB o'.isLB φ₂'), GlobalTheory.CechPic.cls_pull o'.isLB,
      ← Rigid.pull_cls_P m1, ← GlobalTheory.CechPic.pull_comp, h3, Rigid.pull_cls_P m2]
  have act : ∀ c : D.O, Over.Hom.left (o''.act.act c) ≫ φ' = φ' ≫ Over.Hom.left (o'.act.act c) := by
    intro c
    apply m1.cart.1.hom_ext
    · simp only [Category.assoc, reassoc_of% h1, h1, m1.act c, m2.act c]
    · simp only [Category.assoc, h2, Over.w_assoc, Over.w]
  have eta : ∀ y : D.La, Over.Hom.left (o''.eta y) ≫ φ' = g ≫ Over.Hom.left (o'.eta y) := by
    intro y
    apply m1.cart.1.hom_ext
    · simp only [Category.assoc, h1, m2.eta y, m1.eta y]
    · simp [h2]
  exact ⟨⟨φ', φ₂', cart, sq, act, pol, eta⟩⟩
