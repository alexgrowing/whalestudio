import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.LargeAll

set_option maxHeartbeats 800000 in

theorem exists_smul_nonneg_large : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n → ∀ f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n, ∃ s : Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  intro _ D T j Y e o hY _ a n hdom hn f hf
  obtain ⟨s, hs, h⟩ := GlobalTheory.LargeCover.exists_smul_nonneg_all D T j Y e o hY a n hdom hn f hf
  have hsm : (algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F s) • f = s • f :=
    @algebraMap_smul (𝓞 Y.d.c₂.F) _ Y.d.c₂.F _ _ (Rul Y.d.Xo₂ Y.d.c₂) _ _ _ (Formalism.L2.Pj.rulesTower _) s f
  refine ⟨algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F s, by simpa using hs, fun la v hv => ?_⟩
  rw [hsm]
  exact h la v hv

end GlobalTheory.LargeAll
