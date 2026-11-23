import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

section Exp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

abbrev dL (Dw : Datum H) : ℕ := Fintype.card (Lt1 Dw)

def ltIdx (Dw : Datum H) : Lt1 Dw ≃ Fin (dL Dw) := Fintype.equivFin _

def addP {S : Type} [CommRing S] : Fin 1 × Fin (dL Dw) → MvPolynomial (Fin 2 × Fin (dL Dw)) S :=
  fun p => X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2)

def actP {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S] (a : 𝓞 E) :
    Fin 1 × Fin (dL Dw) → MvPolynomial (Fin 1 × Fin (dL Dw)) S :=
  fun p => C (algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)) * X p

variable {S : Type} [CommRing S] [Algebra c.F S]

variable (y : FrPt Xo c S)

structure IsExpChart (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) : Prop where
  zero : ∀ m, homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m) ≫
    x (m + 1) = x m
  law : ∀ m, homAt y.x (jetSubstP m (addP (Dw := Dw) (S := S))) ≫ x m =
    jpt y (dL Dw) x m (0 : Fin 2) * jpt y (dL Dw) x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ Xo.univ.t.act.act a = homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a)) ≫ x m
  tan : ∀ ℓ : Lt1 Dw, IsCombAt y.x
    (fun j : Fin (dL Dw) => (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left)
    (fun j => if j = ltIdx Dw ℓ then 1 else 0) (y.u ℓ.1 ℓ.2)

variable (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G)

abbrev ExpFr (m : ℕ) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (1 : ℤ))

def eAt (e : ∀ m, ExpFr y x m) (m : ℕ) (a : 𝓞 E) :=
  LB.pullGen Xo.univ.t.PP.L _ _ (e m) (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left

def betaφ (a : 𝓞 E) : Fin 4 → (Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) :=
  ![(Xo.univ.t.act.act (1 + a * H.bar a)).left, (Xo.univ.t.act.act a).left, 𝟙 _,
    (Xo.univ.t.act.act (a * H.bar a)).left]

def betaε : Fin 4 → ℤ := ![1, -2, -1, -1]

structure IsExpGauge (e : ∀ m, ExpFr y x m) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
    (e m)
  rig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (e 0) (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)
  coc : ∀ a : 𝓞 E, ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
    ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eAt y x e m (1 + a * H.bar a))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eAt y x e m a) 2)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (e m) (eAt y x e m (a * H.bar a)))))

def IsExpGerm (e : ∀ m, ExpFr y x m) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y (dL Dw) m 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y (dL Dw) m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (e m) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x m) τ (toΓ _ (psJet m f))

end Exp

def expVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type} [CommRing S]
    (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (α : Lt1 Dw →₀ ℕ) : S :=
  (α.prod fun _ n => (n.factorial : S)) *
    MvPowerSeries.coeff (Finsupp.mapDomain (fun ℓ => ((0 : Fin 1), ltIdx Dw ℓ)) α) f

end Formalism.L2.Pj
