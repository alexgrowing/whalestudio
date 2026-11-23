import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_residueTerm_rankinSelberg_innerProduct : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∀ F : GA E a → ℂ, Continuous F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → (∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g) → Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1 : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 ((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) := by
  first | exact @GlobalTheory.RSThetaRes.residue_geometric | exact GlobalTheory.RSThetaRes.residue_geometric | (intros; apply GlobalTheory.RSThetaRes.residue_geometric <;> assumption)
