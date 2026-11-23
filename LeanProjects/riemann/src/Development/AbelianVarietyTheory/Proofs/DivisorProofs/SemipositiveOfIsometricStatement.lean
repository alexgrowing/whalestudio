import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveOfIsometric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semipositive_of_isometric : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L M : GlobalTheory.HermLB p) (D : ℕ), L.Isometric M → L.SemiPos D → M.SemiPos D := by
  first | exact @GlobalTheory.HermLB.Isometric.semiPos | exact GlobalTheory.HermLB.Isometric.semiPos | (intros; apply GlobalTheory.HermLB.Isometric.semiPos <;> assumption)
