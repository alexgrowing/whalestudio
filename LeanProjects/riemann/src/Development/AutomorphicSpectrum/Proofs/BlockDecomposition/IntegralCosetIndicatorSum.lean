import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum

theorem measure_cosetSet_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k) (a : Fin t → k) :
    μ (cosetSet t c a) = μ (cosetSet t c 0) := by
  have h : cosetSet t c a = (fun v => (-a) + v) ⁻¹' cosetSet t c 0 := by
    ext v
    have e : v - a = (-a) + v - 0 := by abel
    show Multiplicative.ofAdd (v - a) ∈ Lc t c ↔ Multiplicative.ofAdd ((-a) + v - 0) ∈ Lc t c
    rw [e]
  rw [h]
  exact MeasureTheory.measure_preimage_add μ (-a) _

theorem smInt_sum_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → ∀ (A : Finset (Fin t → k)) (z : (Fin t → k) → Z), smInt μ (fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => z a) v) = (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) • ∑ a ∈ A, z a := by
  intro k _ _ _ _ t Z _ _ _ _ μ _ c hc A z
  classical
  have hmem : ∀ B : Finset (Fin t → k),
      (fun v => ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) v) ∈ fibM (Fin t → k) Z := by
    intro B
    have h := Submodule.sum_mem (fibM (Fin t → k) Z) (t := B)
      (f := fun a => (cosetSet t c a).indicator (fun _ => z a))
      (fun a _ => (cosetFn t hc a (z a)).2)
    have e : (fun v => ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) v) =
        ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) := by
      funext v
      rw [Finset.sum_apply]
    rw [e]
    exact h
  refine Finset.induction_on A ?_ ?_
  · have h := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator μ (∅ : Set (Fin t → k)) (0 : Z)
    simpa using h
  · intro a B ha ih
    have e : (fun v => ∑ b ∈ insert a B, (cosetSet t c b).indicator (fun _ => z b) v) =
        (cosetSet t c a).indicator (fun _ => z a) +
          fun v => ∑ b ∈ B, (cosetSet t c b).indicator (fun _ => z b) v := by
      funext v
      rw [Finset.sum_insert ha]
      rfl
    have l₁ : IsLocallyConstant ((cosetSet t c a).indicator fun _ => z a) := (cosetFn t hc a (z a)).2.1
    have c₁ : HasCompactSupport ((cosetSet t c a).indicator fun _ => z a) := (cosetFn t hc a (z a)).2.2
    rw [e, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_add μ l₁ c₁ (hmem B).1 (hmem B).2, ih, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator,
      measure_cosetSet_eq t μ c a, Finset.sum_insert ha, smul_add]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum

end
