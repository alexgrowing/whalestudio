import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNefHermitianTwistingSheaf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenNef

theorem isNef_of_gen_small : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ) (s : Fin n → M.B.Sec), M.SemiPos D → (∀ i, s i ∈ M.smallSec) → (∀ x : X, ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.IsNef D := by
  intro _ k _ X _ p D hX M n s hsp hsm hs
  have hcov : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) = ⊤ :=
    top_le_iff.1 fun x _ =>
      have ⟨i, hi⟩ := hs x
      Opens.mem_iSup.2 ⟨i, hi⟩
  exact GlobalTheory.VolBr.Model.isNef_of_small hX M hsp
    (GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX M (GlobalTheory.isGenerated_of_finite s hcov))
    fun x => have ⟨i, hi⟩ := hs x; ⟨s i, hsm i, hi⟩

end GlobalTheory.GenNef

end
