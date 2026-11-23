import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.IsPerfPairOfSurjective
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PerfectField

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem perfect_ring (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) {ψ : LinearMap.BilinForm R (HdR A)} (hψ : IsPolForm (dp0 R) (𝟙 _) A L ψ) (hiso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) (hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A L) : LinearMap.IsPerfPair ψ :=
  perfect_ring_of (fun _ _ _ _ _ hA hg _ hL _ hψ hiso hK ↦ perfect_field hF hH hA hg hL hψ hiso hK)
    hF hH hB hA hg hL hψ hiso hK

end CrystallinePoints.Pd
