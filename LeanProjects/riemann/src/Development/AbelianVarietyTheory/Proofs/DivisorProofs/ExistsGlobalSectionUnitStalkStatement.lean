import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionUnitStalk
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_section_unit_stalk : ∀ (Y Z : Scheme.{0}) (ι : Y ⟶ Z) (D : LB Z), D.IsLB → ∀ t : (D.pull ι).Gen, t.IsGen →
  ∀ (M : ℕ) (a : ∀ i, Γ(Z, D.U i)),
  (∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) * ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j)) →
  ∃ h : Γ(Y, ⊤), ∀ (i : D.ι) (y : Y) (hy : ι y ∈ D.U i), ∃ u : (Y.presheaf.stalk y)ˣ,
    (Y.presheaf.germ ⊤ y trivial).hom h = (ι.stalkMap y).hom ((Z.presheaf.germ (D.U i) (ι y) hy).hom (a i)) * (u : Y.presheaf.stalk y) := by
  first | exact @GlobalTheory.DivGlue.glue | exact GlobalTheory.DivGlue.glue | (intros; apply GlobalTheory.DivGlue.glue <;> assumption)
