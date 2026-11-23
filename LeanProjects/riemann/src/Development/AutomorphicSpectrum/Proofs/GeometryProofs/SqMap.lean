import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Values

variable {X Y F : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

def wv (w : LB.Iso (L.pull f) (M.pull g)) {Z : Scheme.{0}} (ψ : Z ⟶ F) (z : Z) (JL : (Z ⟶ X) → L.ι)
    (JM : (Z ⟶ Y) → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z _ (w.s (fun _ => JM (ψ ≫ g), fun _ => JL (ψ ≫ f)))

def Tr (w : LB.Iso (L.pull f) (M.pull g)) {Y' : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y' ⟶ F))
    (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε))
    (b : LB.Gen (LB.LinComb M φM ε)) (u : Γ(Y', ⊤)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ Y) → M.ι), Good L z JL → Good M z JM →
    val c r z JL * ∏ k, wv w (r ≫ φ k) z JL JM ^ ε k = gm r z ⊤ u * val b r z JM

end Values

section Series

variable {R : Type} [CommRing R] {d d' : ℕ}

def linQ (Qs : Fin d' → PS R 1 d) : Matrix (Fin d') (Fin d) R :=
  fun i l => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), l) 1) (Qs i)

def subQ (Qs : Fin d' → PS R 1 d) (f : PS R 2 d') : PS R 2 d :=
  MvPowerSeries.subst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) f

def sub1 (Qs : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 1 × Fin d') m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (Qs p.2)

def sub2 (Qs : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 2 × Fin d') m →ₐ[R] Jet R (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d' => psIn d m ![p.1] (Qs p.2)

end Series

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev GF : Over (Sp k) := (Over.pullback x).obj t.G

def toF {T : Over (Sp k)} (a : T.left ⟶ t.G.left) (h : a ≫ t.G.hom = T.hom ≫ x) : T ⟶ GF t x :=
  Over.homMk (pullback.lift a T.hom h) (pullback.lift_snd _ _ _)

def fibPt {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) : overAt (𝟙 (Sp k)) A ⟶ GF t x :=
  toF t x y.left (by simpa using Over.w y)

def cubeF {A : Type} [CommRing A] [Algebra k A] (xs : Fin 2 → (overAt x A ⟶ t.G)) (I : ULift (Finset (Fin 2))) :
    Sp A ⟶ (GF t x).left :=
  (fibPt t x (psum t.G xs I.down)).left

def sqPr (p : GF t x ⊗ GF t x ⟶ GF t x) : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G :=
  Over.homMk (p.left ≫ pullback.fst t.G.hom x) (by
    have h : p.left ≫ pullback.snd t.G.hom x = (GF t x ⊗ GF t x).hom := Over.w p
    show (p.left ≫ pullback.fst t.G.hom x) ≫ t.G.hom = (GF t x ⊗ GF t x).hom ≫ x
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])

def sqMap : (GF t x ⊗ GF t x).left ⟶ (t.G ⊗ t.G).left :=
  (lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))).left

def sqPt (a : t.G ⊗ t.G ⟶ t.G) : GF t x ⊗ GF t x ⟶ GF t x :=
  toF t x (sqMap t x ≫ a.left) (Over.w (lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _)) ≫ a))

abbrev AdTy (t : SAB H X) (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

def adF (a : 𝓞 E) : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2)) →
    ((GF t x ⊗ GF t x).left ⟶ (GF t x).left) :=
  Sum.elim (fun I => (sqPt t x (psum t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I.down)).left)
    (fun I => (sqPt t x (psum t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I.down)).left)

def ax0 : (GF t x).left ⟶ (GF t x ⊗ GF t x).left := (lift (1 : GF t x ⟶ GF t x) (𝟙 (GF t x))).left

def ax1 : (GF t x).left ⟶ (GF t x ⊗ GF t x).left := (lift (𝟙 (GF t x)) (1 : GF t x ⟶ GF t x)).left

def qq {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) : (GF t x ⊗ GF t x).left ⟶ (Q.tB.G ⊗ Q.tB.G).left :=
  (lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)).left

end Fibre

section AdRel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def AdRel (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (a : 𝓞 E) (wL : AdTy t a) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.mulGen t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
        (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ u)
        (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end AdRel

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
