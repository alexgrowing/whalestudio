import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRigFr

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRos

section Series

variable {S : Type} [CommRing S] {ρ κ : Type}

def bil [Fintype ρ] (A : ρ → ρ → S) : MvPowerSeries (Fin 2 × ρ) S :=
  ∑ r, ∑ s, MvPowerSeries.C (A r s) * MvPowerSeries.X ((0 : Fin 2), r) * MvPowerSeries.X ((1 : Fin 2), s)

def quad [Fintype ρ] (B : ρ → ρ → S) : MvPowerSeries ρ S :=
  ∑ r, ∑ s, MvPowerSeries.C (B r s) * MvPowerSeries.X r * MvPowerSeries.X s

def qexp [Algebra ℚ S] (q : MvPowerSeries κ S) : MvPowerSeries κ S :=
  PowerSeries.subst q (PowerSeries.exp S)

end Series

section Ratio

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left) {O : Type} [CommRing O]

def ratio6 (bar : O → O) (ch : ρ → O →+* S) {x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G} (e : Fr x0 L x) (c : O) (m : ℕ)
    (y : (overAt x0 (Jet S (Fin 2 × ρ) m)).left)
    (J : ((overAt x0 (Jet S (Fin 2 × ρ) m)).left ⟶ G.left) → L.ι) :
    ((overAt x0 (Jet S (Fin 2 × ρ) m)).left.presheaf.stalk y)ˣ :=
  ev x0 L e ![fun r => ch r c, fun _ => 1] m y J * (ev x0 L e ![fun r => ch r c, fun _ => 0] m y J)⁻¹ *
    (ev x0 L e ![fun _ => 0, fun _ => 1] m y J)⁻¹ * (ev x0 L e ![fun _ => 1, fun r => ch r (bar c)] m y J)⁻¹ *
    ev x0 L e ![fun _ => 1, fun _ => 0] m y J * ev x0 L e ![fun _ => 0, fun r => ch r (bar c)] m y J

def IsBilRatio [Algebra ℚ S] (a : OAct O G) (bar : O → O) (ch : ρ → O →+* S) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G)
    (e : Fr x0 L x) (c : O) (A : ρ → ρ → S)
    (w : LB.Gen (LB.LinComb L (rosatiφ G (a.act c) (a.act (bar c))) rosatiε)) : Prop :=
  w.IsGen ∧ (∀ y J, Good L y J → val w (zero2 G) y J = 1) ∧
    ∀ m y J, Good L y J → (val w (pt2 x0 x m).left y J).val * gs (𝟙 _) y ⊤ (toΓ _ (psJet m (qexp (bil A)))) =
      (ratio6 x0 L bar ch e c m y J).val

end Ratio

end GlobalTheory.RayRos
