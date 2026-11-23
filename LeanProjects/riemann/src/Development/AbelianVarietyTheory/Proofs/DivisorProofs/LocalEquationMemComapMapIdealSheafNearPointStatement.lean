import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEquationMemComapMapIdealSheafNearPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)) (x : M.Z) (i : D.ι), π x ∈ V.1 → x ∈ D.U i → g ∈ (D.idealSheaf.map π).ideal V → valF M₁.pt V.1 g ≠ 0 → valF M.pt (D.U i) (D.f i) / valF M₁.pt V.1 g ∈ M.O x → ∃ (W : M.Z.affineOpens) (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG M.Z h (D.f i) ∈ ((D.idealSheaf.map π).comap π).ideal W := by
  first | exact @GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | exact GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | (intros; apply GlobalTheory.Poinc.resG_f_mem_comap_map_ideal <;> assumption)
