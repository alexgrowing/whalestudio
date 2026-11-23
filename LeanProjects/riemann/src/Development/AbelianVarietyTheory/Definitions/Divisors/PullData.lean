import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolDeg GlobalTheory.TChart

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def CanonOn (Q : Data R) (W : (Sp R).Opens) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) : Prop :=
  P.IsLB ∧ ∃ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R))
    (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O)
    (inc : G ⟶ G') (pr : G' ⟶ G), (∀ y, PsiUnitOn D'.toPre y W) ∧ IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G ∧ pr ≫ inc = oG.act F.e ∧
      LBIso P ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)

variable {Q : Data R} {W W' : (Sp R).Opens} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {P : LB (G2 G).left}

theorem CanonOn.canon (h : CanonOn Q W G P) : Canon Q G P := by
  obtain ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, -, h⟩ := h
  exact ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, h⟩

theorem CanonOn.mono (h : CanonOn Q W G P) (hW : W' ≤ W) : CanonOn Q W' G P := by
  obtain ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, hψ, h⟩ := h
  exact ⟨h₀, D', F, A', G', a, b, U', oA, oG, inc, pr, fun y j V hV hU => hψ y j V hV (hU.trans hW), h⟩

section Pull

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def PullData (Q : Data R) (θ : R →+* V) (Q' : Data V) (e : Q'.X ≃+ Q.X) : Prop :=
  ∃ (β : Q'.B.left ⟶ Q.B.left) (β₂ : (G2 Q'.B).left ⟶ (G2 Q.B).left)
    (w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback Q'.B Q.B (spMap θ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (e a)).left) ∧
    ∀ a b, ∃ (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c (e a)) (Q.c (e b))) negε)) (x y : R) (k : (FractionRing R)ˣ)
      (k' : (FractionRing V)ˣ), u.IsGen ∧ θ y ≠ 0 ∧
      (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x ∧
      (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) ∧
      (∀ z J, Good Q.M.L z J → val (Q.tau (e a) (e b)) (𝟙 _) z J =
        gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) ∧
      ∀ z J J', Good Q.M.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' =
        gm (𝟙 (TK V).left) z ⊤ (unitOn k') *
          (lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' *
            val u ((TK V).hom ≫ spMap θ) z J)

end Pull

end GlobalTheory.Mum
