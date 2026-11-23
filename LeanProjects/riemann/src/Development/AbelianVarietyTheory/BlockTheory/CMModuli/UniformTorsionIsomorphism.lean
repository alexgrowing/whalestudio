import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open scoped CategoryTheory.Obj

def ringActOf {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (a : Geo.Tor.OAct O G) : RingAct G O where
  act := a.act
  hom := a.hom
  map_one := a.one
  map_mul := fun x y => by rw [_root_.mul_comm x y]; exact a.mul y x
  map_add := fun x y => a.add x y

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {R : Type} [CommRing R] [IsDomain R]

structure OData (H : Host E) (I : Ideal R) where

  D : DegData R I

  [mod : Module (𝓞 E) D.toPre.X]

  ac : letI := hostStar H; D.OAct (𝓞 E)
  through : PsiThroughHost H ac

attribute [instance] OData.mod

variable {H : Host E} {I : Ideal R}

structure OUnif (t : SAB H (Spec (CommRingCat.of R))) (Δ : OData H I) where

  A : PolAV (Spec (CommRingCat.of (FractionRing R)))

  actA : letI := hostStar H; A.OAct (𝓞 E)

  U : Unif I Δ.D A t.G
  LG_eq : U.LG = t.PP
  cub_eq : HEq U.cubG t.cub
  lin : letI := hostStar H; U.toUnifPre.OLinear (𝓞 E) Δ.ac actA (ringActOf t.act)

structure PELUnif (I : Ideal R) (t : SAB H (Spec (CommRingCat.of R))) where

  dat : OData H I

  unif : OUnif t dat

section Points

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

def toGen {G : Over (Spec (CommRingCat.of R))} (x : TF (R := R) F ⟶ G) :
    TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift x.left (jFK (R := R) F) (Over.w x)) (pullback.lift_snd _ _ _)

lemma toGen_fst {G : Over (Spec (CommRingCat.of R))} (x : TF (R := R) F ⟶ G) :
    (toGen x).left ≫ pullback.fst G.hom (jK R) = x.left :=
  pullback.lift_fst _ _ _

lemma toGen_injective {G : Over (Spec (CommRingCat.of R))} :
    Function.Injective (toGen (R := R) (F := F) (G := G)) := fun x y h => by
  ext
  rw [← toGen_fst x, ← toGen_fst y, h]

end Points

namespace OUnif

variable {t : SAB H (Spec (CommRingCat.of R))} {Δ : OData H I} (u : OUnif t Δ)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def ptA (x : TF (R := R) F ⟶ t.G) : TFK (R := R) F ⟶ u.A.A := toGen x ≫ u.U.gen.hom

lemma ptA_injective : Function.Injective (u.ptA F) := fun _ _ h =>
  toGen_injective ((cancel_mono u.U.gen.hom).1 h)

def ToAk (k : ℕ) (p : QkPt Δ.D.toPre F k) (x : TF (R := R) F ⟶ t.G) : Prop :=
  QkToAkU u.U.toUnifPre F k p (u.ptA F x)

structure TorsIso (k : ℕ) : Prop where

  total : ∀ p : QkPt Δ.D.toPre F k, ∃! x : TF (R := R) F ⟶ t.G, u.ToAk F k p x

  onto : ∀ x : TF (R := R) F ⟶ t.G, x ^ k = 1 ↔ ∃ p : QkPt Δ.D.toPre F k, u.ToAk F k p x

  inj : ∀ (p p' : QkPt Δ.D.toPre F k) (x x' : TF (R := R) F ⟶ t.G),
    u.ToAk F k p x → u.ToAk F k p' x' → (QkPt.Equiv Δ.D.toPre F p p' ↔ x' = x)

  add : ∀ (p p' p'' : QkPt Δ.D.toPre F k) (x x' x'' : TF (R := R) F ⟶ t.G),
    u.ToAk F k p x → u.ToAk F k p' x' → u.ToAk F k p'' x'' → (QkAdd p p' p'' ↔ x'' = x * x')

  smul : ∀ (a : 𝓞 E) (p p' : QkPt Δ.D.toPre F k) (x x' : TF (R := R) F ⟶ t.G),
    u.ToAk F k p x → u.ToAk F k p' x' →
      ((letI := hostStar H; QkSmul Δ.ac a p p') ↔ x' = x ≫ t.act.act a)

  weil : ∀ (p p' : QkPt Δ.D.toPre F k) (x x' : TF (R := R) F ⟶ t.G),
    u.ToAk F k p x → u.ToAk F k p' x' → ∀ ζ : Fˣ,
      (WeilIs t.G t.PP.L (k : ℤ) x x' (unitOn ζ) ↔ WeilQkIs Δ.D.toPre F k p p' (ζ : F))

def TorsClause : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    u.TorsIso F k

example (h : u.TorsIso F 1) (p : QkPt Δ.D.toPre F 1) : u.ToAk F 1 p 1 := by
  obtain ⟨x, hx, -⟩ := h.total p
  have h1 : x ^ 1 = 1 := (h.onto x).2 ⟨p, hx⟩
  rw [pow_one] at h1
  exact h1 ▸ hx

end OUnif

abbrev PELUnif.ToAk {t : SAB H (Spec (CommRingCat.of R))} (P : PELUnif I t) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (p : QkPt P.dat.D.toPre F k)
    (x : TF (R := R) F ⟶ t.G) : Prop := P.unif.ToAk F k p x

abbrev PELUnif.TorsClause {t : SAB H (Spec (CommRingCat.of R))} (P : PELUnif I t) : Prop :=
  P.unif.TorsClause

end GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism
