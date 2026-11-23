import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolDeg GlobalTheory.TChart

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

structure PFactor (Q : Data R) (D' : DegPre R) where

  O : Type
  [ring : Ring O]
  [star : StarRing O]
  [mod : Module O D'.X]

  o : D'.OAct O

  e : O

  f : O

  inc : Q.B ⟶ (letI := D'.P.isAb.comm; D'.P.A)

  pr : D'.P.A ⟶ Q.B

  xi : Q.X →+ D'.X

  xp : D'.X →+ Q.X

  w : letI := D'.P.isAb.comm
    LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ D'.P.A D'.P.L).pull
      (lift (fst Q.B Q.B ≫ inc) (snd Q.B Q.B ≫ inc ≫ o.onB.act f) : G2 Q.B ⟶ G2 D'.P.A).left)
  idem : e * e = e
  inc_hom : IsMonHom inc
  pr_hom : IsMonHom pr
  inc_pr : inc ≫ pr = 𝟙 _
  pr_inc : pr ≫ inc = o.onB.act e
  xp_xi : ∀ y, xp (xi y) = y
  xi_xp : ∀ z, xi (xp z) = e • z
  c_xi : ∀ y, D'.c (xi y) = Q.c y ≫ inc
  inj : Function.Injective fun y => Star.star e • f • xi y
  onto : ∀ z, ∃ y, Star.star e • z = Star.star e • f • xi y
  w_gen : w.IsGen
  tau : ∀ a b z J J', Good D'.P.L z J → Good Q.M.L z J' →
    val (Q.tau a b) (𝟙 _) z J' =
      lamVal w (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J J' *
        val (D'.tau (xi a) (f • xi b)) (𝟙 _) z J
  alg : (∃ b : ℕ, 0 < b ∧ Star.star e * e = b • (Star.star e * f * e)) ∧
    Star.star e * f * e = Star.star e * Star.star f * e ∧ ∃ g : O, g * (Star.star e * f * e) = e

attribute [instance] PFactor.ring PFactor.star PFactor.mod

def Canon [IsLocalRing R] (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) : Prop :=
  P.IsLB ∧ ∃ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R))
    (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O)
    (inc : G ⟶ G') (pr : G' ⟶ G), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsMonHom inc ∧ IsMonHom pr ∧
      inc ≫ pr = 𝟙 G ∧ pr ≫ inc = oG.act F.e ∧
      LBIso P ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)

theorem Canon.isLB [IsLocalRing R] {Q : Data R} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {P : LB (G2 G).left}
    (h : Canon Q G P) : P.IsLB := h.1

def PFactor.ofFactor {D D' : DegPre R} (F : Factor D D') (hF : F.Alg) (hB : D.TauBimult) :
    PFactor (PolDeg.Wit.ofDeg D hB) D' where
  O := F.O; o := F.o; e := F.e; f := F.f; inc := F.inc; pr := F.pr; xi := F.xi; xp := F.xp; w := F.w
  idem := F.idem; inc_hom := F.inc_hom; pr_hom := F.pr_hom; inc_pr := F.inc_pr; pr_inc := F.pr_inc
  xp_xi := F.xp_xi; xi_xp := F.xi_xp; c_xi := F.c_xi; inj := F.inj; onto := F.onto; w_gen := F.w_gen
  tau a b z J J' hJ hJ' := ((PolDeg.Wit.exists_tau D a b).choose_spec.2 _ _ z J' hJ').trans (F.tau a b z J J' hJ hJ')
  alg := hF

theorem PFactor.ofFactor_e {D D' : DegPre R} (F : Factor D D') (hF : F.Alg) (hB : D.TauBimult) :
    (PFactor.ofFactor F hF hB).e = F.e ∧ (PFactor.ofFactor F hF hB).f = F.f := ⟨rfl, rfl⟩

def Wit.pfac : PFactor (PolDeg.Wit.ofDeg InhTate.tatePre InhTate.tauBimult) Wit.tate2 :=
  PFactor.ofFactor Wit.fac Wit.fac_alg InhTate.tauBimult

theorem Wit.pfac_e : Wit.pfac.e ≠ 0 ∧ Wit.pfac.e ≠ 1 := Wit.fac_e

example : Wit.pfac.f = (1 : ℤ × ℤ) := rfl

example : Wit.pfac.O = (ℤ × ℤ) := rfl

end GlobalTheory.Mum
