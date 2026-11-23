import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ChartDiv

theorem chart_ratio_mem_O : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (a : Fin (n + 1)) (z : M.Z), PCrd (M.pt ≫ h) c → z ∈ h ⁻¹ᵁ chart k n a → c a ≠ 0 ∧ ∀ z' ∈ h ⁻¹ᵁ chart k n a, ∀ b, c b / c a ∈ M.O z' := by
  intro k Ω _ _ _ M n c h a z hc hz
  have hx : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ chart k n a := M.top_le_preimage_pt (U := h ⁻¹ᵁ chart k n a) ⟨z, hz⟩
  obtain ⟨ha, hb⟩ := GlobalTheory.UMin.CrdChart.pCrd_chart k Ω n (M.pt ≫ h) c a hc hx
  refine ⟨ha, fun z' hz' b => ?_⟩
  rw [← hb b, Points.valR_comp, ← Points.valF_eq_valR]
  exact RatModel.valF_mem_O hz' _

end GlobalTheory.UMin.ChartDiv
