import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem baseChange_eighthPower_product_monHom : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (G H : Over S) [GrpObj G] [GrpObj H] (pr : Fin 8 → (G ⟶ H)), (∀ a, IsMonHom (pr a)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ pr a = y a) → (∀ a, IsMonHom ((Over.pullback t).map (pr a))) ∧ ∀ (T : Over S') (y : Fin 8 → (T ⟶ (Over.pullback t).obj H)), ∃! x : T ⟶ (Over.pullback t).obj G, ∀ a, x ≫ (Over.pullback t).map (pr a) = y a := by
  intro S S' t G H _ _ pr hmon hlim
  refine ⟨fun a => by haveI := hmon a; infer_instance, ?_⟩
  let c : Fan (fun _ : Fin 8 => H) := Fan.mk G pr
  have hc : IsLimit c := by
    refine Fan.IsLimit.mk c (fun s => (hlim s.pt s.proj).choose) (fun s j => ?_) (fun s m hm => ?_)
    · exact (hlim s.pt s.proj).choose_spec.1 j
    · exact (hlim s.pt s.proj).choose_spec.2 m hm
  intro T y
  let s : Fan (fun _ : Fin 8 => (Over.pullback t).obj H) := Fan.mk T y
  have hs : IsLimit (Fan.mk ((Over.pullback t).obj G) (fun a => (Over.pullback t).map (pr a))) :=
    isLimitFanMkObjOfIsLimit (Over.pullback t) (fun _ : Fin 8 => H) pr hc
  refine ⟨hs.lift s, fun a => hs.fac s ⟨a⟩, fun x hx => ?_⟩
  exact hs.uniq s x (by rintro ⟨a⟩; exact hx a)

end GlobalTheory
