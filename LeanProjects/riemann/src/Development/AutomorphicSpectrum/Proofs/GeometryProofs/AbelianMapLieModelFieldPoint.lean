import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CombVal

section General

variable {S S' : Scheme.{0}} {G : CategoryTheory.Over S} {G' : CategoryTheory.Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem push_mul (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b)
    (x y : CategoryTheory.Over.mk a ⟶ G') (x₀ y₀ : CategoryTheory.Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hab
  exact h.2 (CategoryTheory.Over.mk a) x y x₀ y₀ hx hy

theorem push_one (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b) :
    (1 : CategoryTheory.Over.mk b ⟶ G).left = (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ := by
  subst hab
  exact (congrArg (fun z => z.left) (map_one (pushHom h (CategoryTheory.Over.mk a)))).symm

theorem one_left_congr {A : Scheme.{0}} {a b : A ⟶ S} (h : a = b) :
    (1 : CategoryTheory.Over.mk a ⟶ G).left = (1 : CategoryTheory.Over.mk b ⟶ G).left := by
  subst h
  rfl

theorem push_mul₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) (x y : CategoryTheory.Over.mk a ⟶ G') (x' y' : CategoryTheory.Over.mk a₂ ⟶ G₂)
    (hx : x.left ≫ φ = x'.left ≫ φ₂) (hy : y.left ≫ φ = y'.left ≫ φ₂) :
    (x * y).left ≫ φ = (x' * y').left ≫ φ₂ := by
  have wx : (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w x]
    rfl
  have wy : (y.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w y]
    rfl
  let W : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (x.left ≫ φ) wx
  let W' : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (y.left ≫ φ) wy
  exact (push_mul h rfl x y W W' rfl rfl).symm.trans (push_mul h₂ hab.symm x' y' W W' hx hy)

theorem push_one₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) :
    (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ = (1 : CategoryTheory.Over.mk a₂ ⟶ G₂).left ≫ φ₂ :=
  (push_one h hab).symm.trans (push_one h₂ rfl)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {F : Type} [Field F] [Algebra c.F F]

abbrev qe (y : FrPt Xo c F) : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.XF c :=
  spMap (algebraMap F (DualNumber F)) ≫ Small.ptF y

theorem qe_fst (y : FrPt Xo c F) : qe y ≫ pullback.fst _ _ = spMap (algebraMap F (DualNumber F)) ≫ y.x := by
  rw [Category.assoc, Small.ptF_fst]

def liftP (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G :=
  CategoryTheory.Over.homMk (Y.m0.cart.1.lift p.left (qe y) ((CategoryTheory.Over.w p).trans (qe_fst y).symm)) (Y.m0.cart.1.lift_snd _ _ _)

theorem pointLift_fst (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) :
    (liftP Y y p).left ≫ Y.m0.toSABMap.φ = p.left :=
  Y.m0.cart.1.lift_fst _ _ _

theorem pointLift_eq (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) (P : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G)
    (h : P.left ≫ Y.m0.toSABMap.φ = p.left) : (liftP Y y p).left = P.left := by
  apply Y.m0.cart.1.hom_ext
  · exact (pointLift_fst Y y p).trans h.symm
  · exact (CategoryTheory.Over.w (liftP Y y p)).trans (CategoryTheory.Over.w P).symm

variable {Y : Model Xo c β} {X : Scheme.{0}} {tX : SAB H X} {f : X ⟶ Y.X} (m : SABMap tX Y.t f)
  {g : Spec (CommRingCat.of F) ⟶ X} {EC : Type} [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC)
  (y : FrPt Xo c F)

def Rd (p : tEps y.x ⟶ Xo.univ.t.G) (e : EC) : Prop :=
  (MC.pt e).left ≫ m.φ = (liftP Y y p).left ≫ Y.m.φ

variable {y}

theorem base_eq (hY : Small.ptY Y y = g ≫ f) :
    (spMap (algebraMap F (DualNumber F)) ≫ g) ≫ f = qe y ≫ Y.jQ ≫ pullback.fst _ _ := by
  rw [Category.assoc, Category.assoc, ← hY]
  rfl

theorem pt_zero : MC.pt 0 = 1 := by
  have h := MC.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem rd_one (hY : Small.ptY Y y = g ≫ f) : Rd m MC y 1 0 := by
  have h1 : (liftP Y y 1).left = (1 : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G).left := by
    refine pointLift_eq Y y 1 1 ?_
    exact ((push_one Y.m0.cart (qe_fst y)).symm).trans (one_left_congr rfl)
  unfold Rd
  rw [h1, pt_zero]
  exact push_one₂ m.cart Y.m.cart (base_eq hY)

theorem rd_mul (hY : Small.ptY Y y = g ≫ f) {p p' : tEps y.x ⟶ Xo.univ.t.G} {e e' : EC}
    (h : Rd m MC y p e) (h' : Rd m MC y p' e') : Rd m MC y (p * p') (e + e') := by
  have h1 : (liftP Y y (p * p')).left = (liftP Y y p * liftP Y y p').left := by
    refine pointLift_eq Y y _ _ ?_
    exact (push_mul Y.m0.cart (qe_fst y) (liftP Y y p) (liftP Y y p') p p'
      (pointLift_fst Y y p).symm (pointLift_fst Y y p').symm).symm
  unfold Rd
  rw [h1, MC.add]
  exact push_mul₂ m.cart Y.m.cart (base_eq hY) (MC.pt e) (MC.pt e') (liftP Y y p) (liftP Y y p') h h'

theorem scale_base (a : F) : spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap F (DualNumber F)) =
    spMap (algebraMap F (DualNumber F)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem rd_smul {p p₂ : tEps y.x ⟶ Xo.univ.t.G} {e : EC} (a : F)
    (hp : p₂.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ p.left) (h : Rd m MC y p e) :
    Rd m MC y p₂ (a • e) := by
  have h1 : (liftP Y y p₂).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (liftP Y y p).left := by
    apply Y.m0.cart.1.hom_ext
    · rw [pointLift_fst, Category.assoc, pointLift_fst, hp]
    · have e₁ := CategoryTheory.Over.w (liftP Y y p)
      have e₂ := CategoryTheory.Over.w (liftP Y y p₂)
      refine e₂.trans ?_
      rw [Category.assoc, e₁]
      show qe y = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ qe y
      rw [qe, ← Category.assoc, scale_base]
  unfold Rd at h ⊢
  rw [h1, MC.smul, Category.assoc, Category.assoc, h]
  rfl

theorem rd_prod (hY : Small.ptY Y y = g ≫ f) :
    ∀ (n : ℕ) (u : Fin n → (tEps y.x ⟶ Xo.univ.t.G)) (e : Fin n → EC), (∀ i, Rd m MC y (u i) (e i)) →
      Rd m MC y (List.ofFn u).prod (∑ i, e i)
  | 0, u, e, _ => by
    simpa using rd_one m MC hY
  | n + 1, u, e, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact rd_mul m MC hY (h 0) (rd_prod hY n _ _ fun i => h i.succ)

end CombVal

theorem comb_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, Formalism.L2.Pj.IsTanAt y.x (v j)) (e : Fin n → EC), (∀ j, (MC.pt (e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y (v j) (hv j).1) → ∀ (cf : Fin n → F) (w : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left), IsCombAt y.x v cf w → ∃ hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y.x, (MC.pt (∑ j, cf j • e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y w hw := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hY n v hv e he cf w hc
  obtain ⟨u, hu, rfl⟩ := hc
  refine ⟨CategoryTheory.Over.w ((List.ofFn u).prod), ?_⟩
  have h0 : ∀ j, CombVal.Rd m MC y (CategoryTheory.Over.homMk (v j) (hv j).1 : tEps y.x ⟶ Xo.univ.t.G) (e j) := he
  have h1 : ∀ j, CombVal.Rd m MC y (u j) (cf j • e j) := fun j => CombVal.rd_smul m MC (cf j) (hu j) (h0 j)
  exact CombVal.rd_prod m MC hY n u (fun j => cf j • e j) h1

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
