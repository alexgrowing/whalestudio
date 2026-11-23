import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfKillsTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtOverClosureIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem actG_mem_laHat {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {g : G.GAf}
    (hg : g ∈ L.KN N) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : L.actG g v ∈ LaHat D := by
  obtain ⟨w, hw, e⟩ := hg.1 v hv
  rw [e]
  exact add_mem hv (nsmul_mem hw N)

end GlobalTheory.LKGeo
