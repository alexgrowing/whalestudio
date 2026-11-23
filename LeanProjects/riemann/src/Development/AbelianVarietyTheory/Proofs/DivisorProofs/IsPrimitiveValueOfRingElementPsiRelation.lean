import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic

namespace GlobalTheory.Mum.PowData

def AdjCls {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [GrpObj G₀] (c : Pic G.left) (c₀ : Pic G₀.left) (q : G ⟶ G₀)
    (j : G₀ ⟶ G) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G) (z : T ⟶ G₀), lam c x (z ≫ j) = lam c₀ (x ≫ q) z

variable {R : Type} [CommRing R] [IsDomain R]

def PrimVal (D : DegPre R) (f : D.P.A ⟶ D.P.A) (m : D.X → D.X) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) f).left, 𝟙 D.P.A.left, f.left, (toUnit D.P.A ≫ η[D.P.A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ ∀ y, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau y (m y)) (LB.pullGen D.P.L _ _ u (D.xK y))) (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)

theorem isPrimitiveValue_of_ringElement_psiRelation {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X] {o : D.OAct O} {w : O}
    (h : TraceFormTwistIso D o w) : PrimVal D (o.onB.act w) (fun y => w • y) :=
  h.imp fun _ h => ⟨h.1, h.2.2⟩

def Expand (D : DegPre R) {K : Type} [Fintype K] (n : K → ℤ) {T : Over (Sp R)} (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)) : Prop :=
  ∃ κ : LB.Gen (LB.LinComb D.P.L (Sum.elim (lamPts x (∏ i, y i ^ n i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
      (Sum.elim Oε (fun k : K × Fin 4 => -(n k.1 * Oε k.2)))),
    κ.IsGen ∧ ∀ (p : TK R ⟶ T) (a : D.X) (b : K → D.X), p ≫ x = toUnit _ ≫ D.c a → (∀ i, p ≫ y i = toUnit _ ≫ D.c (b i)) →
      ∀ z J, Good D.P.L z J →
        val (D.tau a (∑ i, n i • b i)) (𝟙 _) z J * val κ p.left z J = ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ n i

def CmpTwo (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A) : Prop :=
  ∃ Γ : LB.Gen (LB.LinComb (JN D D₀)
      (Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
        (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)) (Sum.elim Oε Oinvε)),
    Γ.IsGen ∧ ∀ (χ' : D.X) (χ : D₀.X), D.c χ' = D₀.c χ ≫ j → ∀ u : LB.Gen (CmpLB D D₀ q χ' χ), Nrm u →
      ∀ (T : Over (Sp R)) (x : T ⟶ D.P.A) (z : T.left) (J), Good (JN D D₀) z J →
        val u x.left z J = val Γ (lift x (toUnit T ≫ D₀.c χ)).left z J

def PeriodRel (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (h : D₀.X → D.X) (k : D.X → D₀.X) : Prop :=
  ∀ χ, ∃ u : LB.Gen (CmpLB D D₀ q (h χ) χ), Nrm u ∧ ∀ y z J, Good (JN D D₀) z J →
    val (D₀.tau (k y) χ) (𝟙 _) z (rr J) = val (D.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D.c y)) z J

section Points

variable {S : Scheme.{0}} {T T' G G' : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K]

theorem comp_prod_zpow (p : T' ⟶ T) (y : K → (T ⟶ G)) (n : K → ℤ) : p ≫ ∏ i, y i ^ n i = ∏ i, (p ≫ y i) ^ n i := by
  let f : (T ⟶ G) →* (T' ⟶ G) := MonoidHom.mk' (fun a => p ≫ a) fun a b => MonObj.comp_mul p a b
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

theorem prod_zpow_comp [GrpObj G'] [IsCommMonObj G'] (y : K → (T ⟶ G)) (n : K → ℤ) (g : G ⟶ G') [IsMonHom g] :
    (∏ i, y i ^ n i) ≫ g = ∏ i, (y i ≫ g) ^ n i := by
  let f : (T ⟶ G) →* (T ⟶ G') := MonoidHom.mk' (fun a => a ≫ g) fun a b => MonObj.mul_comp a b g
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

end Points

end GlobalTheory.Mum.PowData
