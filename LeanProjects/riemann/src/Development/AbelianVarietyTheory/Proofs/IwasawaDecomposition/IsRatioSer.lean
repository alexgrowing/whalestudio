import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRigFr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBilRatio

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz GlobalTheory.RayRos
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRosEx

section Series

variable {S : Type} [CommRing S] {ρ : Type}

def ser3 (M : Fin 2 → Fin 3 → S) (F : MvPowerSeries (Fin 2 × ρ) S) : MvPowerSeries (Fin 3 × ρ) S :=
  MvPowerSeries.subst
    (fun p : Fin 2 × ρ => ∑ i : Fin 3, MvPowerSeries.C (M p.1 i) * MvPowerSeries.X (i, p.2)) F

def LawL (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ser3 ![![1, 1, 0], ![0, 0, 1]] F = ser3 ![![1, 0, 0], ![0, 0, 1]] F * ser3 ![![0, 1, 0], ![0, 0, 1]] F

def LawR (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ser3 ![![1, 0, 0], ![0, 1, 1]] F = ser3 ![![1, 0, 0], ![0, 1, 0]] F * ser3 ![![1, 0, 0], ![0, 0, 1]] F

end Series

section Ratio

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left) {O : Type} [CommRing O]

def IsRatioSer (bar : O → O) (ch : ρ → O →+* S) {x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G} (e : Fr x0 L x) (c : O)
    {φ : Fin 6 → ((G ⊗ G).left ⟶ G.left)} (w : LB.Gen (LB.LinComb L φ rosatiε))
    (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ∀ m y J, Good L y J → (val w (pt2 x0 x m).left y J).val * gs (𝟙 _) y ⊤ (toΓ _ (psJet m F)) =
    (ratio6 x0 L bar ch e c m y J).val

end Ratio

end GlobalTheory.RayRosEx
