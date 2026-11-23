import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

noncomputable section

namespace UpperTheory.AlgHT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

abbrev th (V : Type) [CommRing V] [IsLocalRing V] (e : ℕ) :
    Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) ⟶ Sp V :=
  Out.thick V (IsLocalRing.maximalIdeal V) e

abbrev thT (V : Type) [CommRing V] [IsLocalRing V] (e : ℕ) :
    Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) ⟶ Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1 + 1)) :=
  Out.thickTrans V (IsLocalRing.maximalIdeal V) e

structure Tow (b : Base D R) (N : ℕ) (V : Type) [CommRing V] [IsLocalRing V] (s : Sp V ⟶ Sp R) where

  σ : ∀ e : ℕ, Sp (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) ⟶ Sp R
  hσ : ∀ e, σ e = th V e ≫ s

  o : ∀ e : ℕ, Obj b N (σ e)

  m : ∀ e : ℕ, ObjMap (o e) (o (e + 1)) (thT V e)

variable {b : Base D R} {N : ℕ} {V : Type} [CommRing V] [IsLocalRing V] {s : Sp V ⟶ Sp R}

structure TowAb (t : Tow b N V s) where
  A : Over (Sp V)
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A

  b : ∀ e, (t.o e).A.left ⟶ A.left
  cart : ∀ e, IsGrpPullback (t.o e).A A (th V e) (b e)
  tr : ∀ e, (t.m e).φ ≫ b (e + 1) = b e

  M : LB A.left
  isLBM : M.IsLB
  ample : Out.RelAmple A M
  Mi : ∀ e, LBIso ((t.o e).P.pull (lift (𝟙 (t.o e).A) (𝟙 (t.o e).A)).left) (M.pull (b e))

attribute [instance] TowAb.grp TowAb.comm

structure TowAlg (t : Tow b N V s) extends TowAb t where
  act : OActN D.O A
  act_b : ∀ e c, ((t.o e).act.act c).left ≫ b e = b e ≫ (act.act c).left
  P : LB (G2 A).left
  isLB : P.IsLB

  b₂ : ∀ e, (G2 (t.o e).A).left ⟶ (G2 A).left
  sq : ∀ e, IsSquare (b e) (b₂ e)
  pol : ∀ e, LBIso (t.o e).P (P.pull (b₂ e))
  eta : D.La → (𝟙_ (Over (Sp V)) ⟶ A)
  eta_b : ∀ e y, ((t.o e).eta y).left ≫ b e = th V e ≫ (eta y).left

end UpperTheory.AlgHT
