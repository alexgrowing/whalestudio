import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CenOrd

def IsLab {g n : ℕ} {F : SFam g n (zetaAway n)} {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω}
    (ρ : S.Real) {s' : Sp S.R ⟶ Sp (cycAway n)} (c : SiegPre g n (zetaAway n) s') (pr : Fin 8 → (ρ.P.A ⟶ c.A))
    (φc : c.A.left ⟶ F.univ.A.left) (T : Trait F) (h : Sp (FractionRing T.V) ⟶ Sp S.R) (a : S.Gam) (v : Fin 8)
    (χ : T.D.toPre.X) : Prop :=
  ∃ (pk : QkPt T.D.toPre (AlgebraicClosure (FractionRing T.V)) (S.r * S.N))
    (z : TFK (R := T.V) (AlgebraicClosure (FractionRing T.V)) ⟶ T.A.A),
    pk.y = χ ∧ QkToAkU T.U.toUnifPre (AlgebraicClosure (FractionRing T.V)) (S.r * S.N) pk z ∧
      z.left ≫ T.α = spMap (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) ≫ h ≫
        (ρ.pt a ≫ pr v).left ≫ φc

end GlobalTheory.Poinc.CenOrd
