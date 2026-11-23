import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormShiftRationalMultipleLog
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_shift_rational_multiple_log : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : HeightOneSpectrum (𝓞 F) → ℝ), Norms V L₁ f a l → Norms V L₂ f a (fun v e y => l v e y + c v) → ∀ v, ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * c v = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.CoverNorm.const_rat | exact GlobalTheory.CoverNorm.const_rat | (intros; apply GlobalTheory.CoverNorm.const_rat <;> assumption)
