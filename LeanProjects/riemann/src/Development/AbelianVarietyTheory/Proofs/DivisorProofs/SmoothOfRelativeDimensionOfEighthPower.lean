import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowDim

theorem smoothOfRelativeDimension_of_eighthPower : ∀ {S : Scheme.{0}} [IsIntegral S] (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)) (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) (hG : IsSemiAbelian G) (hH : SmoothOfRelativeDimension (8 * g) H.hom), SmoothOfRelativeDimension g G.hom := by
  intro S _ G H _ _ g pr huniv hG hH
  have hlim : IsLimit (Fan.mk H pr) :=
    mkFanLimit _ (fun s => (huniv s.pt s.proj).choose) (fun s i => (huniv s.pt s.proj).choose_spec.1 i)
      (fun s m hm => (huniv s.pt s.proj).choose_spec.2 m hm)
  let e : H ≅ powObj G 8 := hlim.conePointUniqueUpToIso (powIsLimit G 8)
  have hw : H.hom = e.hom.left ≫ (powObj G 8).hom := (Over.w e.hom).symm
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : ConnectedSpace S := inferInstance
  haveI : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨s⟩ : Nonempty S := inferInstance
  obtain ⟨n, hn⟩ := Geo.Tor.exists_dim_of_preconnected G.hom (eSec G s)
  have h8 := smoothOfRelativeDimension_powObj G n hn 8
  have h2 : SmoothOfRelativeDimension (0 + 8 * n) H.hom := by
    rw [hw]; infer_instance
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ hH h2 (eSec H s)
  have hgn : g = n := by omega
  subst hgn
  exact hn

end GlobalTheory.PowDim
