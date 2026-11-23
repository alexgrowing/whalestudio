import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyWeightSectionProducts
import Mathlib
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_weight_section_products : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ Y.V (wtOf _ la 0), ∀ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F) (eu : Ix (T.Q.Dw j) → ℤ), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ eu → t ≠ 0 → u * u' = t • 1 → ∃ K : ℕ, ∀ k, K ≤ k → ∀ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t' : Y.d.c₂.F) (w : GlobalTheory.AllWt.Weight (T.Q.Dw j)), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) w 0) → t' ≠ 0 → φ * φ' = t' • 1 → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) w 0) kk) (rdU (Y.U σ) φ kk) y ≤ C) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → f ^ (k + 1) * (u * φ) ∈ sec Y.d.Xo₂ Y.d.c₂ a n → f ^ (k + 1) * (u * φ) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
  first | exact @GlobalTheory.CuspMulUnit.pow_mul_mem_cusp | exact GlobalTheory.CuspMulUnit.pow_mul_mem_cusp | (intros; apply GlobalTheory.CuspMulUnit.pow_mul_mem_cusp <;> assumption)
