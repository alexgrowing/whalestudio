import Development.WeilBound.CoreStatements.HodgeTatePoints.Weilfun
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace PositivityTheory.HtPt.Weilreg

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    GlobalTheory.CompanionTheory.Ar.BT.valAt x ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (x.appTop.hom s) := by
  rfl

theorem val_unitOn {R : Type} [CommRing R] (u : Rˣ) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((unitOn u : Γ(Sp R, ⊤)ˣ) : Γ(Sp R, ⊤)) = (u : R) := by
  simp [unitOn]

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
  {G : Over S} [GrpObj G] {y : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

def toAmb (h : Γ.IsTorsionAlong G y N i) {Y : Over (Spec (CommRingCat.of R))} (x : Y ⟶ Γ.G) :
    Over.mk (Y.hom ≫ y) ⟶ G :=
  Over.homMk (x.left ≫ i) (by
    change (x.left ≫ i) ≫ G.hom = Y.hom ≫ y
    rw [Category.assoc, h.isOver, ← Category.assoc, Over.w x])

theorem toAmb_pow (h : Γ.IsTorsionAlong G y N i) {Y : Over (Spec (CommRingCat.of R))} (x : Y ⟶ Γ.G) :
    toAmb h x ^ N = 1 :=
  (h.kernel Y _).2 ⟨x, rfl⟩

def overMap (y : Spec (CommRingCat.of R) ⟶ S) {Y Y' : Over (Spec (CommRingCat.of R))} (f : Y' ⟶ Y) :
    Over.mk (Y'.hom ≫ y) ⟶ Over.mk (Y.hom ≫ y) :=
  Over.homMk f.left (by
    change f.left ≫ Y.hom ≫ y = Y'.hom ≫ y
    rw [← Category.assoc, Over.w f])

theorem overMap_toAmb (h : Γ.IsTorsionAlong G y N i) {Y Y' : Over (Spec (CommRingCat.of R))} (f : Y' ⟶ Y)
    (x : Y ⟶ Γ.G) : overMap y f ≫ toAmb h x = toAmb h (f ≫ x) := by
  ext1
  simp [overMap, toAmb]

theorem weil_regular_of_fun (hW : type_of% @PositivityTheory.HtPt.Weilfun.weil_fun) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (La : Type) [AddCommGroup La] (X : TorsTower p t.G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ y)) → (∀ n (a b : La) (ga gb : Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G), ga.left = ((X.Γ n).pt (lev p n a)).left ≫ X.i n → gb.left = ((X.Γ n).pt (lev p n b)).left ≫ X.i n → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) ga gb (unitOn (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ n ^ B a b)))) → X.PairingRegular B ζ := by
  intro E _ _ _ H S _ t p _ O _ _ _ y La _ X B ζ hP hWe n
  have hpos : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨w, hnat, hval⟩ := hW E H S t (p ^ n) hpos
  let Y : Over (Spec (CommRingCat.of O)) := (X.Γ n).G ⊗ (X.Γ n).G
  let a0 : Over.mk (Y.hom ≫ y) ⟶ t.G := toAmb (X.tors n) (fst (X.Γ n).G (X.Γ n).G)
  let b0 : Over.mk (Y.hom ≫ y) ⟶ t.G := toAmb (X.tors n) (snd (X.Γ n).G (X.Γ n).G)
  refine ⟨(w (Over.mk (Y.hom ≫ y)) a0 b0 (toAmb_pow _ _) (toAmb_pow _ _)).val, ?_⟩
  intro a b
  let q : BT.genPt O ⟶ Y := lift ((X.Γ n).pt (lev p n a)) ((X.Γ n).pt (lev p n b))
  have ha : overMap y q ≫ a0 = toAmb (X.tors n) ((X.Γ n).pt (lev p n a)) := by
    simp only [a0, overMap_toAmb, q, lift_fst]
  have hb : overMap y q ≫ b0 = toAmb (X.tors n) ((X.Γ n).pt (lev p n b)) := by
    simp only [b0, overMap_toAmb, q, lift_snd]
  have key := hnat _ _ (overMap y q) a0 b0 (toAmb_pow _ _) (toAmb_pow _ _)
    (by rw [ha]; exact toAmb_pow _ _) (by rw [hb]; exact toAmb_pow _ _)
  have hw := hval (FractionRing O) ((BT.genPt O).hom ≫ y) hP
    (toAmb (X.tors n) ((X.Γ n).pt (lev p n a))) (toAmb (X.tors n) ((X.Γ n).pt (lev p n b)))
    (toAmb_pow _ _) (toAmb_pow _ _) _ (hWe n a b _ _ rfl rfl)
  rw [valAt_top]
  change (Scheme.ΓSpecIso (CommRingCat.of (FractionRing O))).hom.hom
      ((overMap y q).left.appTop.hom (w (Over.mk (Y.hom ≫ y)) a0 b0 _ _).val) = _
  rw [← key]
  have e : w _ (overMap y q ≫ a0) (overMap y q ≫ b0)
      (by rw [ha]; exact toAmb_pow _ _) (by rw [hb]; exact toAmb_pow _ _) =
      w _ (toAmb (X.tors n) ((X.Γ n).pt (lev p n a))) (toAmb (X.tors n) ((X.Γ n).pt (lev p n b)))
      (toAmb_pow _ _) (toAmb_pow _ _) := by
    congr 1
  rw [e, hw, val_unitOn]
  rfl

theorem weil_regular : type_of% (weil_regular_of_fun @PositivityTheory.HtPt.Weilfun.weil_fun) :=
  weil_regular_of_fun @PositivityTheory.HtPt.Weilfun.weil_fun

end PositivityTheory.HtPt.Weilreg
