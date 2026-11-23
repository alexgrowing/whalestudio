import Development.EtaleCohomology.EtaleSheaves.LeafConsPf
import Development.EtaleCohomology.EtaleSheaves.LeafConsPfA

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafConsPfB
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafConsPfA

theorem rpl_congr (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') {u u2 : U' ⟶ U} {e e2 : E' ⟶ E}
    (hu : u = u2) (he : e = e2) (c : f' ≫ e = u ≫ f) (c2 : f' ≫ e2 = u2 ≫ f) (n : ℤ) (y) :
    rpl q i f f' u e c n y = rpl q i f f' u2 e2 c2 n y := by
  subst hu he; rfl

instance (B : Scheme.{0}) : IsIso (top B).hom := by show IsIso (Iso.refl B).hom; infer_instance

abbrev uT {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    pullback (pullback.snd p (top B).hom ≫ (top B).hom) ι ⟶ pullback p ι :=
  pullback.map _ ι p ι (pullback.fst p (top B).hom) (𝟙 W) (𝟙 B) (by rw [Category.comp_id, pullback.condition]) (by simp)

theorem uT_comm {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    prU p ι (top B) ≫ pullback.fst p (top B).hom = uT p ι ≫ pullback.fst p ι := (pullback.lift_fst _ _ _).symm

instance {Y B : Scheme.{0}} (p : Y ⟶ B) : IsIso (pullback.fst p (top B).hom) := by infer_instance
instance {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) : IsIso (uT p ι) := by infer_instance

theorem rpl_comp' (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (n : ℤ) (y) :
    rpl q i f' f'' u' e' c' n (rpl q i f f' u e c n y) =
      rpl q i f f'' (u' ≫ u) (e' ≫ e) (by rw [← Category.assoc, c', Category.assoc, c, Category.assoc]) n y :=
  (rpl_comp q i f f' f'' u e u' e' c c' _ n y).symm

abbrev TT (q : ℕ) (i : ℤ) {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (n : ℤ) :=
  rpl q i (pullback.fst p ι) (prU p ι (top B)) (uT p ι) (pullback.fst p (top B).hom) (uT_comm p ι) n

abbrev TL (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) (n : ℤ) :=
  rpl q i ι (prB ι (top B)) (pullback.snd (top B).hom ι) (top B).hom pullback.condition n

set_option maxHeartbeats 800000 in
theorem L1 {B Y0 Y1 Y2 : Scheme.{0}} (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) :
    pullback.fst (g2 ≫ g1 ≫ p) (top B).hom ≫ g2 ≫ g1 =
      mY (g1 ≫ p) g2 (top B) ≫ mY p g1 (top B) ≫ pullback.fst p (top B).hom := by
  simp only [mY, pullback.map]
  erw [pullback.lift_fst, pullback.lift_fst_assoc]
  simp only [Category.assoc]

set_option maxHeartbeats 800000 in
theorem L3 {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    uT p ι ≫ pullback.snd p ι = toBW p ι (top B) ≫ pullback.snd (top B).hom ι := by
  simp only [uT, toBW, pullback.map]
  erw [pullback.lift_snd, pullback.lift_snd]

set_option maxHeartbeats 800000 in
theorem L2 {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) :
    uT (g2 ≫ g1 ≫ p) ι ≫ pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp) =
      mW (g1 ≫ p) g2 ι (top B) ≫ mW p g1 ι (top B) ≫ uT p ι := by
  apply pullback.hom_ext
  · have := L1 p g1 g2
    simp only [mY] at this
    simp only [uT, mW, mY, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.map]
  · simp only [uT, mW, mY, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map]
    simp

theorem LeafGlob_pf : LateralTheory.E.LeafConsPf.LeafGlob := by
  intro q _ i B W Y0 Y1 Y2 ι _ p g1 g2 K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  refine ⟨fun n y => l0 (top B) n (TT q i p ι n y), fun n y => l2 (top B) n (TT q i (g2 ≫ g1 ≫ p) ι n y),
    fun n c => lL (top B) n (TL q i ι n c), ?_, ?_, ?_, ?_⟩
  · intro n
    exact (r2.1 _ n).1.comp (rpl_bij _ _ _ _ _ _ _ _).1
  · intro n
    exact (rL.1 _ n).2.comp (rpl_bij _ _ _ _ _ _ _ _).2
  · intro n y
    have h1 := mf (top B) n (TT q i p ι n y)
    have h2 := mg (top B) n (rpl q i (prU p ι (top B)) (prU (g1 ≫ p) ι (top B)) (mW p g1 ι (top B)) (mY p g1 (top B))
      (pullback.lift_fst _ _ _).symm n (TT q i p ι n y))
    show l2 (top B) n _ = l0 (top B) n (TT q i p ι n y) ≫ (shiftFunctor _ n).map (f ≫ g)
    rw [Functor.map_comp]
    refine Eq.trans ?_ (Category.assoc _ _ _)
    rw [← h1, ← h2]
    refine congrArg (l2 (top B) n) ?_
    rw [rpl_comp', rpl_comp', rpl_comp']
    apply rpl_congr
    · simpa only [Category.assoc] using L2 ι p g1 g2
    · simpa only [Category.assoc] using L1 p g1 g2
  · intro n c
    have h := mℓ (top B) n (TL q i ι n c)
    refine Eq.trans ?_ h
    refine congrArg (l2 (top B) n) ?_
    rw [rpl_comp', rpl_comp']
    apply rpl_congr
    · simpa only [Category.assoc] using L3 (g2 ≫ g1 ≫ p) ι
    · simp only [toBY]; exact pullback.condition

end LateralTheory.E.LeafConsPfB
