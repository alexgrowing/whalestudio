import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem mapsAt₂_val : ∀ (Y X X₁ X₂ Z : Scheme.{0}) (L : LB X) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ) (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))) (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))), MapsAt₂ w p n a b₁ b₂ → ∀ (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι), Good L z J → Good L₁ z J₁ → Good L₂ z J₂ → val b₁ r z J₁ * val b₂ r z J₂ = gm (r ≫ p) z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)), J (r ≫ p))) ^ n * val a r z J := by
  intro Y X X₁ X₂ Z L L₁ L₂ f₁ f₂ w p n a b₁ b₂ hM r z J J₁ J₂ hJ hJ₁ hJ₂
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U
      (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)), J (r ≫ p)) :=
    ⟨⟨Set.mem_iInter.2 fun _ => hJ₁ (r ≫ p ≫ f₁), Set.mem_iInter.2 fun _ => hJ₂ (r ≫ p ≫ f₂)⟩, hJ (r ≫ p)⟩
  have e := congrArg (gm r z _) (hM (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)) (J (r ≫ p)))
  rw [map_mul, map_mul, map_zpow] at e
  exact (congrArg₂ (· * ·) (gm_res r z _ hm _) (gm_res r z _ hm _)).symm.trans
    (e.trans (congrArg₂ (· * ·) (congrArg (· ^ n) (gm_pull r p z _ hm _)) (gm_res r z _ hm _)))

end GlobalTheory.MumProd
