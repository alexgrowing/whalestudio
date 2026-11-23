import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev Fib (Xo : Moduli Dw l) {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : Over (Sp K) :=
  (Over.pullback x).obj Xo.univ.t.G

variable {Xo : Moduli Dw l} {c : Coeff l}

def Lin {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') : Prop :=
  ∀ a : 𝓞 E, (Over.pullback x).map (Xo.univ.t.act.act a) ≫ f = f ≫ (Over.pullback x').map (Xo.univ.t.act.act a)

def IsPair (N : ℕ) {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) : Prop :=
  IsMonHom f ∧ IsMonHom f' ∧ f ≫ f' = 𝟙 _ ^ N ∧ f' ≫ f = 𝟙 _ ^ N ∧ Lin f ∧ Lin f'

example {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : IsPair 1 (𝟙 (Fib Xo x)) (𝟙 _) :=
  ⟨inferInstance, inferInstance, by simp, by simp, fun _ => by simp, fun _ => by simp⟩

def HkWith (p : ℕ) {K : Type} [Field K] [Algebra c.F K] (y z : FrPt Xo c K) (f : Fib Xo y.x ⟶ Fib Xo z.x)
    (f' : Fib Xo z.x ⟶ Fib Xo y.x) : Prop :=
  IsPair (p ^ 2) f f' ∧ (∀ τ j, IsLieImageH p f.left (y.u τ j) (z.u τ j)) ∧
    IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) p y.s z.s

def HkOver (p : ℕ) {K : Type} [Field K] [Algebra c.F K] (y z : FrPt Xo c K) : Prop :=
  AllRat Xo y.x (p ^ 2) ∧ AllRat Xo z.x (p ^ 3) ∧ ∃ f f', HkWith p y z f f'

def IsBC {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {x x' : Sp K ⟶ Xo.X} {w w' : Sp L ⟶ Xo.X}
    (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') : Prop :=
  w = spMap φ ≫ x ∧ w' = spMap φ ≫ x' ∧
    ∀ (π : pullback Xo.univ.t.G.hom w ⟶ pullback Xo.univ.t.G.hom x)
      (π' : pullback Xo.univ.t.G.hom w' ⟶ pullback Xo.univ.t.G.hom x'),
      π ≫ pullback.fst _ _ = pullback.fst _ _ → π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ →
      π' ≫ pullback.fst _ _ = pullback.fst _ _ → π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ →
      (g.left : pullback Xo.univ.t.G.hom w ⟶ pullback Xo.univ.t.G.hom w') ≫ π' =
        π ≫ (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')

def Ext {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') (F : G.G ⟶ G'.G) : Prop :=
  ∃ ψ : t.G ⟶ t'.G, IsMonHom ψ ∧ ψ.left ≫ n₂.φ = m₂.φ ≫ F.left ∧
    ∀ (g : t.G.left ⟶ pullback Xo.univ.t.G.hom x) (g' : t'.G.left ⟶ pullback Xo.univ.t.G.hom x'),
      g ≫ pullback.fst _ _ = m₁.φ → g ≫ pullback.snd _ _ = t.G.hom →
      g' ≫ pullback.fst _ _ = n₁.φ → g' ≫ pullback.snd _ _ = t'.G.hom →
      g ≫ (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = ψ.left ≫ g'

def Reg {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))) : Prop :=
  ∃ σ, PullbackSections.SecTie I (M ^ 2) (PullbackSections.zCast Xo.univ.t.G (PullbackSections.natCast_sq M) F) σ

def IsTransl (M : ℕ) {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} (s : LB.Sec (PPx x))
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ a, IsVtOver Xo.univ.t.G Xo.univ.t.PP M (fun u => u ^ (M ^ 2) = 1) s a F

def IsPullOf (M : ℕ) {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (a : K)
    (s' : LB.Sec (PPx x')) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) ((M : ℤ) ^ 2))) (s'' : LB.Sec (PPx x')),
    IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) _ β ∧ (∀ i, s''.f i = scal x' a i * s'.f i) ∧
      IsCarried Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) _ β s'' t

def IsTranslSum (M : ℕ) {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} (s : LB.Sec (PPx x))
    (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ (n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))),
    (∀ i, IsTransl M s (F i)) ∧ ∀ j, t.f j = ∑ i, (F i).f j

end GlobalTheory.HkIntegral
