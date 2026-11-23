import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatioCover

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r := by
  intro A _ g L u hA
  haveI := hA.comm
  obtain ⟨H, _, m, s, hv⟩ := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA
  refine ⟨m + 1, fun k => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k),
    fun k j => GlobalTheory.ProjSpace.secRatio (s k) (s j), fun k => (hv.2 k).1, hv.1,
    fun k j => GlobalTheory.ProjSpace.basicOpen_secRatio _ _, fun k => GlobalTheory.ProjSpace.secRatio_self _, ?_⟩
  intro k j l z hk hj
  have hkj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) ⊓ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s j)) :=
    (GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hk, hj⟩
  have e := congrArg (valAt' (u.ex z).left _)
    (GlobalTheory.ProjSpace.secRatio_mul_secRatio (s k) (s j) (s l) (inf_le_left) (inf_le_right))
  rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hkj, GlobalTheory.valAt'_res _ _ _ hkj, GlobalTheory.valAt'_res _ _ _ hkj] at e
  exact e.symm

end GlobalTheory.RatioCover
