import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure MultiWit (Y : Model Xo c β) {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} (a : ArcIn Dw l β A b) {r : ℕ}
    (δ : Fin r → LinearMap.BilinForm ℤ a.D₀.X) {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (f : A →+* R)
    (u : Fin r → R) {R' : Type} [CommRing R'] (ι : R →+* R') (y : Sp R' ⟶ Xo.XF c) where

  t : SAB H (Sp R)

  t' : SAB H (Sp R')

  m₁ : SABMap t' t (spMap ι)

  m₂ : SABMap t' Y.t (y ≫ Y.j)

  P : PELUnif I t

  φ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left

  he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A

  w : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ)

  e : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X

  spec :
    letI := H.starRing
    IsGrpPullback P.D.toPre.P.A a.D₀.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.D.toPre.P.A) (fun _ => 1)) P.D.toPre.rig
      (rigPullOf φ (spMap f) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (P.oD.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ x, (P.D.toPre.c (e x)).left ≫ φ = spMap f ≫ (a.D₀.c x).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing A) F] (uF : Fin r → F),
      (∀ x, algebraMap (FractionRing A) F (algebraMap A _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
      (∀ i, uF i = algebraMap (FractionRing R) F (algebraMap R _ (u i))) →
      (∀ x, GenRel w (LB.pullGen _ _ _ (P.D.toPre.psi (e x)) (Out.jFK (R := R) F))
        (LB.pullGen _ _ _ (a.D₀.psi x) (Out.jFK (R := A) F)) (∏ i, uF i ^ (δ i x x / 2))) ∧
      ∀ (s : R' →+* F), (∀ x, s (ι x) = algebraMap (FractionRing R) F (algebraMap R _ x)) →
        ∀ (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing A) k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G),
          ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
            (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
              HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v)) →
          ∀ (q₀ : Out.QkPt a.D₀ F k) (q : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := R) F ⟶ P.A.A)
            (x' : Sp F ⟶ t'.G.left),
            QkExt (algebraMap _ F) p₀ q₀ → q.y = e q₀.y →
            (∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (∏ i, uF i ^ (δ i q₀.y z / k))) →
            x' ≫ t'.G.hom = spMap s →
            x' ≫ m₁.φ = x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) →
            x' ≫ m₂.φ = spMap s ≫ y ≫ σ.left ≫ Y.m.φ →
            P.ToA F k q x

section General

variable {Y : Model Xo c β} {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : A →+* R} {R' : Type} [CommRing R'] {ι : R →+* R'}
  {y : Sp R' ⟶ Xo.XF c}

theorem nonempty_multiWit_of_arcWit {u : R} {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (hy : y ≫ Y.j = spMap ι ≫ χ) :
    Nonempty (MultiWit Y a (fun _ : Fin 1 => a.be) I f (fun _ => u) ι y) := by
  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab (spMap ι) W.t
  obtain ⟨m', hm'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ W.m m₁
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : SABMap t' Y.t (y ≫ Y.j), m₂.φ = m₁.φ ≫ W.m.φ := by
    rw [hy]; exact ⟨m', hm'⟩
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  refine ⟨⟨W.t, t', m₁, m₂, W.P, W.φ, W.he, W.w, W.e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF hF hu => ?_⟩⟩
  obtain ⟨k₁, k₂⟩ := s6 F (uF 0) hF (hu 0)
  refine ⟨fun x => by simpa only [Fin.prod_univ_one] using k₁ x,
    fun s hs k p₀ σ hσ q₀ q x x' e₁ e₂ e₃ _ e₅ e₆ => k₂ (spMap s ≫ y) ?_ k p₀ σ hσ q₀ q x e₁ e₂
      (fun z => by simpa only [Fin.prod_univ_one] using e₃ z) ?_⟩
  · rw [Category.assoc, hy, ← Category.assoc, ← spMap_comp, ← Category.assoc, ← spMap_comp]
    exact congrArg (fun q => spMap q ≫ χ) (RingHom.ext hs)
  · rw [Category.assoc, ← e₆, hm₂, reassoc_of% e₅]

variable {r : ℕ} {δ : Fin r → LinearMap.BilinForm ℤ a.D₀.X} {u : Fin r → R}

def MultiWit.LieImg (W : MultiWit Y a δ I f u ι y) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR R ⟶ W.t.G) : Prop :=
  ∀ (n : ℕ) (vn : Sp (DualNumber (R ⧸ I ^ (n + 1))) ⟶ (Out.thickObj R I n W.t.G).left),
    vn ≫ (Out.fstG I n W.t.G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ v.left →
    ∀ x, GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn)
      (LB.pullGen _ _ _ (ν.s x) (spMap (dualMap ((Ideal.Quotient.mk (I ^ (n + 1))).comp f))))

def MultiWit.IsSpecOf (W : MultiWit Y a δ I f u ι y) {γ : levelForms H l.M' a.D₀.X} {h : γ ∈ admitted H l.M' a.D₀.X}
    {R₁ : Type} [CommRing R₁] [IsDomain R₁] {I₁ : Ideal R₁} {f₁ : A →+* R₁} {u₁ : R₁} {χ : Sp R₁ ⟶ Y.X}
    (W₁ : ArcWit Y (withForm a γ h) I₁ f₁ u₁ χ) (g : R →+* R₁) (m₀ : SABMap W₁.t W.t (spMap g))
    {R₁' : Type} [CommRing R₁'] (ι₁ : R₁ →+* R₁') (g' : R' →+* R₁') : Prop :=
  (∃ (hD : Out.IsPullDeg g W.P.D.toPre W₁.P.D.toPre) (bc : W₁.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G)
    (w₁ : LB.Iso W₁.P.D.toPre.P.L
      (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ))),
    IsMonHom bc.hom ∧ Out.IsPullUnif g hD bc W.P.U W₁.P.U ∧
    m₀.φ = bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g) ∧ (∀ x, hD.xe (W₁.e x) = W.e x) ∧
    W₁.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ ∧ HEq W₁.w w₁ ∧ Tri W.w hD.w w₁) ∧
  ∀ (T : Scheme.{0}) (s : T ⟶ Sp R₁') (z₁ : T ⟶ W₁.t.G.left) (z' : T ⟶ W.t'.G.left),
    z₁ ≫ W₁.t.G.hom = s ≫ spMap ι₁ → z' ≫ W.t'.G.hom = s ≫ spMap g' → z₁ ≫ m₀.φ = z' ≫ W.m₁.φ →
    z₁ ≫ W₁.m.φ = z' ≫ W.m₂.φ

end General

instance MultiRing.isDomain_series (K : Type) [Field K] (r : ℕ) : IsDomain (MvPowerSeries (Fin r) K) :=
  GlobalTheory.CohenStructure.isDomain_mvPowerSeries K r

abbrev SerWit (Y : Model Xo c β) {K : Type} [Field K] {b : O →+* K} (a : ArcIn Dw l β K b) {r : ℕ}
    (δ : Fin r → LinearMap.BilinForm ℤ a.D₀.X) (y : Sp (MultiRing K r) ⟶ Xo.XF c) :=
  MultiWit Y a δ (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) (MvPowerSeries.C (σ := Fin r) (R := K))
    MvPowerSeries.X (algebraMap (MvPowerSeries (Fin r) K) (MultiRing K r)) y

theorem exists_multiWit {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F) (hY : (Y Z.i).N4) {γ : t.Forms} (h : γ ∈ t.Dir) :
    ∃ y, Nonempty (MultiWit (Y Z.i) (withForm t.a γ h) (fun _ : Fin 1 => γ.1) (Ideal.span {PowerSeries.X})
      (PowerSeries.C (R := F.O)) (fun _ => PowerSeries.X) F.toLaurent y) := by
  obtain ⟨x, v, _, ϖ, χ, Wt, -, -, -, -, hx, -, hfl⟩ := exists_isArc t hY h
  obtain ⟨g, y, -, hy, -⟩ := exists_isFrame_of_flagAt hfl
  exact ⟨y, nonempty_multiWit_of_arcWit Wt (hy.trans hx)⟩

end GlobalTheory.LocM.FJ
