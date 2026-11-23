import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRigFr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrRatio
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayHoriz.CubeNorm

variable {S : Type} [CommRing S] {ρ : Type}

def linSub {K K' : Type} (a : K → Finset K') (F : MvPowerSeries (K × ρ) S) : MvPowerSeries (K' × ρ) S :=
  MvPowerSeries.subst (fun p : K × ρ =>
    ∑ i ∈ a p.1, (MvPowerSeries.X (i, p.2) : MvPowerSeries (K' × ρ) S)) F

def sumSer {K : Type} (I : Finset K) (h : MvPowerSeries ρ S) : MvPowerSeries (K × ρ) S :=
  MvPowerSeries.subst (fun r : ρ => ∑ i ∈ I, (MvPowerSeries.X (i, r) : MvPowerSeries (K × ρ) S)) h

def IsCubSer (F : MvPowerSeries (Fin 3 × ρ) S) : Prop :=
  linSub (K' := Fin 3) ![{0}, {1}, ∅] F = 1 ∧
  linSub (K' := Fin 3) ![{1}, {0}, {2}] F = F ∧
  linSub (K' := Fin 3) ![{0}, {2}, {1}] F = F ∧
  linSub (K' := Fin 4) ![{0, 1}, {2}, {3}] F * linSub (K' := Fin 4) ![{0}, {1}, {3}] F =
    linSub (K' := Fin 4) ![{0}, {1, 2}, {3}] F * linSub (K' := Fin 4) ![{1}, {2}, {3}] F

def IsCubeOf (F : MvPowerSeries (Fin 3 × ρ) S) (h : MvPowerSeries ρ S) : Prop :=
  F * (sumSer (∅ : Finset (Fin 3)) h * sumSer {0, 1} h * sumSer {0, 2} h * sumSer {1, 2} h) =
    sumSer {0} h * sumSer {1} h * sumSer {2} h * sumSer {0, 1, 2} h

section Ratios

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left)

def CubeRatio (t : LB.Gen (Theta G L)) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x)
    (F : MvPowerSeries (Fin 3 × ρ) S) : Prop :=
  ∀ m y J, Good L y J → (val t (GlobalTheory.RayHoriz.pt3 x0 x m).left y J).val =
    gs (𝟙 _) y ⊤ (toΓ _ (psJet m F)) *
      (∏ I : Finset (Fin 3), val (e m) (homAt x0 (jetSum I : Jet S ρ m →ₐ[S] Jet S (Fin 3 × ρ) m)).left y J ^
        ((-1 : ℤ) ^ (3 - I.card))).val

def SymRatio (σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]))
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) (H : MvPowerSeries ρ S) : Prop :=
  ∀ m y J, Good L y J → (val σ (x m).left y J).val =
    gs (𝟙 _) y ⊤ (toΓ _ (psJet m H)) *
      (val (e m) (homAt x0 (jetScale (fun _ => (-1 : S)) : Jet S ρ m →ₐ[S] Jet S ρ m)).left y J *
        (val (e m) (𝟙 _) y J)⁻¹).val

end Ratios

end GlobalTheory.RayHoriz.CubeNorm
